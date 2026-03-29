Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import sll_merge_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import ast_lib.
Require Import malloc.
Require Import super_poly_sll2.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import safeexec_strategy_goal.
From SimpleC.EE Require Import safeexec_strategy_proof.

(*----- Function subst_var -----*)

Definition subst_var_safety_wit_1 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition subst_var_safety_wit_2 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition subst_var_safety_wit_3 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition subst_var_safety_wit_4 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition subst_var_safety_wit_5 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 <> (termtypeID (trm))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  [| False |]
.

Definition subst_var_return_wit_1 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) ,
  [| (retval = (list_Z_cmp (qvar) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |] 
  &&  [| (retval = 0) |]
  &&  (store_string y qvar )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  (store_string den_pre den_str )
|--
  [| (t_pre = t_pre) |]
  &&  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
.

Definition subst_var_return_wit_2 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = z) |] 
  &&  [| (retval = (list_Z_cmp (qvar) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |] 
  &&  [| (retval <> 0) |]
  &&  (store_term z (term_subst_v (den_str) (src_str) (qterm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
  **  (store_string y qvar )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> retval_2)
|--
  [| (t_pre = t_pre) |]
  &&  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
.

Definition subst_var_return_wit_3 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (z: Z) (y: Z) (lt: term) (rt: term) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = z) |] 
  &&  [| (retval = y) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  (store_term z (term_subst_v (den_str) (src_str) (rt)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
  **  (store_term y (term_subst_v (den_str) (src_str) (lt)) )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> retval_2)
|--
  [| (t_pre = t_pre) |]
  &&  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
.

Definition subst_var_return_wit_4 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (typ: const_type) (con: Z) ,
  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermConst (typ) (con))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  [| (t_pre = t_pre) |]
  &&  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
.

Definition subst_var_return_wit_5 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (y: Z) (var: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (list_Z_cmp (var) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  (store_string y var )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string den_pre den_str )
|--
  [| (t_pre = t_pre) |]
  &&  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
.

Definition subst_var_return_wit_6 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (var: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = (list_Z_cmp (var) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  (store_string den_pre den_str )
  **  (store_string retval_2 den_str )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> retval_2)
|--
  [| (t_pre = t_pre) |]
  &&  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
.

Definition subst_var_partial_solve_wit_1 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) ,
  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |]
  &&  (store_term t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |]
  &&  (store_term t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
.

Definition subst_var_partial_solve_wit_2_pure := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  [| ((termtypeID (trm)) = 0) |] 
  &&  [| (t_pre <> 0) |]
.

Definition subst_var_partial_solve_wit_2_aux := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  [| ((termtypeID (trm)) = 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
.

Definition subst_var_partial_solve_wit_2 := subst_var_partial_solve_wit_2_pure -> subst_var_partial_solve_wit_2_aux.

Definition subst_var_partial_solve_wit_3 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (y: Z) (var: (@list Z)) ,
  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string y var )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  (store_string y var )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string den_pre den_str )
.

Definition subst_var_partial_solve_wit_4_pure := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (y: Z) (var: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (list_Z_cmp (var) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  (store_string y var )
  **  (store_string src_pre src_str )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string den_pre den_str )
|--
  [| (y <> 0) |]
.

Definition subst_var_partial_solve_wit_4_aux := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (y: Z) (var: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (list_Z_cmp (var) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  (store_string y var )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string den_pre den_str )
|--
  [| (y <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = (list_Z_cmp (var) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  (store_string y var )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string den_pre den_str )
.

Definition subst_var_partial_solve_wit_4 := subst_var_partial_solve_wit_4_pure -> subst_var_partial_solve_wit_4_aux.

Definition subst_var_partial_solve_wit_5 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (y: Z) (var: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (list_Z_cmp (var) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string den_pre den_str )
|--
  [| (retval = 0) |] 
  &&  [| (retval = (list_Z_cmp (var) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
.

Definition subst_var_partial_solve_wit_6_pure := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 = (termtypeID (trm))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  [| ((termtypeID (trm)) = 1) |] 
  &&  [| (t_pre <> 0) |]
.

Definition subst_var_partial_solve_wit_6_aux := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  [| ((termtypeID (trm)) = 1) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
.

Definition subst_var_partial_solve_wit_6 := subst_var_partial_solve_wit_6_pure -> subst_var_partial_solve_wit_6_aux.

Definition subst_var_partial_solve_wit_7_pure := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
.

Definition subst_var_partial_solve_wit_7_aux := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
.

Definition subst_var_partial_solve_wit_7 := subst_var_partial_solve_wit_7_pure -> subst_var_partial_solve_wit_7_aux.

Definition subst_var_partial_solve_wit_8_pure := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (z: Z) (y: Z) (lt: term) (rt: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term y lt )
  **  (store_term z rt )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (y <> 0) |]
.

Definition subst_var_partial_solve_wit_8_aux := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (z: Z) (y: Z) (lt: term) (rt: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term y lt )
  **  (store_term z rt )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (y <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  (store_term y lt )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term z rt )
.

Definition subst_var_partial_solve_wit_8 := subst_var_partial_solve_wit_8_pure -> subst_var_partial_solve_wit_8_aux.

Definition subst_var_partial_solve_wit_9_pure := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (z: Z) (y: Z) (lt: term) (rt: term) (retval: Z) ,
  [| (retval = y) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  (store_term y (term_subst_v (den_str) (src_str) (lt)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term z rt )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
|--
  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (z <> 0) |]
.

Definition subst_var_partial_solve_wit_9_aux := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (z: Z) (y: Z) (lt: term) (rt: term) (retval: Z) ,
  [| (retval = y) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  (store_term y (term_subst_v (den_str) (src_str) (lt)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term z rt )
|--
  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (z <> 0) |] 
  &&  [| (retval = y) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  (store_term z rt )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
  **  (store_term y (term_subst_v (den_str) (src_str) (lt)) )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
.

Definition subst_var_partial_solve_wit_9 := subst_var_partial_solve_wit_9_pure -> subst_var_partial_solve_wit_9_aux.

Definition subst_var_partial_solve_wit_10_pure := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  [| ((termtypeID (trm)) = 3) |] 
  &&  [| (t_pre <> 0) |]
.

Definition subst_var_partial_solve_wit_10_aux := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  [| ((termtypeID (trm)) = 3) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
.

Definition subst_var_partial_solve_wit_10 := subst_var_partial_solve_wit_10_pure -> subst_var_partial_solve_wit_10_aux.

Definition subst_var_partial_solve_wit_11 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |]
  &&  (store_string y qvar )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  (store_string den_pre den_str )
.

Definition subst_var_partial_solve_wit_12_pure := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) ,
  [| (retval = (list_Z_cmp (qvar) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |] 
  &&  [| (retval <> 0) |]
  &&  (store_string y qvar )
  **  (store_string src_pre src_str )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string den_pre den_str )
|--
  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (z <> 0) |]
.

Definition subst_var_partial_solve_wit_12_aux := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) ,
  [| (retval = (list_Z_cmp (qvar) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |] 
  &&  [| (retval <> 0) |]
  &&  (store_string y qvar )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  (store_string den_pre den_str )
|--
  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (z <> 0) |] 
  &&  [| (retval = (list_Z_cmp (qvar) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |] 
  &&  [| (retval <> 0) |]
  &&  (store_term z qterm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
  **  (store_string y qvar )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
.

Definition subst_var_partial_solve_wit_12 := subst_var_partial_solve_wit_12_pure -> subst_var_partial_solve_wit_12_aux.

Definition subst_var_which_implies_wit_1 := 
forall (trm: term) (t: Z) ,
  (store_term t trm )
|--
  [| (t <> 0) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
.

Definition subst_var_which_implies_wit_2 := 
forall (trm: term) (t: Z) ,
  [| ((termtypeID (trm)) = 0) |] 
  &&  [| (t <> 0) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
|--
  EX (y: Z)  (var: (@list Z)) ,
  [| (t <> 0) |] 
  &&  [| (trm = (TermVar (var))) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string y var )
.

Definition subst_var_which_implies_wit_3 := 
forall (trm: term) (t: Z) ,
  [| ((termtypeID (trm)) = 1) |] 
  &&  [| (t <> 0) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
|--
  EX (typ: const_type)  (con: Z) ,
  [| (t <> 0) |] 
  &&  [| (trm = (TermConst (typ) (con))) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con)
.

Definition subst_var_which_implies_wit_4 := 
forall (trm: term) (t: Z) ,
  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t <> 0) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
|--
  EX (z: Z)  (y: Z)  (lt: term)  (rt: term) ,
  [| (t <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term y lt )
  **  (store_term z rt )
.

Definition subst_var_which_implies_wit_5 := 
forall (trm: term) (t: Z) ,
  [| ((termtypeID (trm)) = 3) |] 
  &&  [| (t <> 0) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
|--
  EX (z: Z)  (y: Z)  (qt: quant_type)  (qvar: (@list Z))  (qterm: term) ,
  [| (t <> 0) |] 
  &&  [| (trm = (TermQuant (qt) (qvar) (qterm))) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
.

(*----- Function subst_term -----*)

Definition subst_term_safety_wit_1 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition subst_term_safety_wit_2 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition subst_term_safety_wit_3 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition subst_term_safety_wit_4 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition subst_term_safety_wit_5 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 <> (termtypeID (trm))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| False |]
.

Definition subst_term_return_wit_1 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) ,
  [| (retval = (list_Z_cmp (qvar) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |] 
  &&  [| (retval = 0) |]
  &&  (store_string y qvar )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  (store_term den_pre den_term )
|--
  (store_term t_pre (term_subst_t (den_term) (src_str) (trm)) )
  **  (store_term den_pre den_term )
  **  (store_string src_pre src_str )
.

Definition subst_term_return_wit_2 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (retval_2: Z) ,
  [| (retval = (list_Z_cmp (qvar) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |] 
  &&  [| (retval <> 0) |]
  &&  (store_term retval_2 (term_subst_t (den_term) (src_str) (qterm)) )
  **  (store_term den_pre den_term )
  **  (store_string src_pre src_str )
  **  (store_string y qvar )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> retval_2)
|--
  (store_term t_pre (term_subst_t (den_term) (src_str) (trm)) )
  **  (store_term den_pre den_term )
  **  (store_string src_pre src_str )
.

Definition subst_term_return_wit_3 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) (lt: term) (rt: term) (retval: Z) (retval_2: Z) ,
  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  (store_term retval_2 (term_subst_t (den_term) (src_str) (rt)) )
  **  (store_term den_pre den_term )
  **  (store_string src_pre src_str )
  **  (store_term retval (term_subst_t (den_term) (src_str) (lt)) )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> retval_2)
|--
  (store_term t_pre (term_subst_t (den_term) (src_str) (trm)) )
  **  (store_term den_pre den_term )
  **  (store_string src_pre src_str )
.

Definition subst_term_return_wit_4 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) (typ: const_type) (con: Z) ,
  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermConst (typ) (con))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con)
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  (store_term t_pre (term_subst_t (den_term) (src_str) (trm)) )
  **  (store_term den_pre den_term )
  **  (store_string src_pre src_str )
.

Definition subst_term_return_wit_5 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) (y: Z) (var: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (list_Z_cmp (var) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  (store_string y var )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_term den_pre den_term )
|--
  (store_term t_pre (term_subst_t (den_term) (src_str) (trm)) )
  **  (store_term den_pre den_term )
  **  (store_string src_pre src_str )
.

Definition subst_term_return_wit_6 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) (var: (@list Z)) (retval_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| (retval_2 = (list_Z_cmp (var) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  (store_term den_pre den_term )
  **  (store_term retval den_term )
  **  (store_string src_pre src_str )
|--
  (store_term retval (term_subst_t (den_term) (src_str) (trm)) )
  **  (store_term den_pre den_term )
  **  (store_string src_pre src_str )
.

Definition subst_term_partial_solve_wit_1 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) ,
  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |]
  &&  (store_term t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |]
  &&  (store_term t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
.

Definition subst_term_partial_solve_wit_2_pure := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| ((termtypeID (trm)) = 0) |] 
  &&  [| (t_pre <> 0) |]
.

Definition subst_term_partial_solve_wit_2_aux := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| ((termtypeID (trm)) = 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
.

Definition subst_term_partial_solve_wit_2 := subst_term_partial_solve_wit_2_pure -> subst_term_partial_solve_wit_2_aux.

Definition subst_term_partial_solve_wit_3 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) (y: Z) (var: (@list Z)) ,
  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string y var )
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  (store_string y var )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_term den_pre den_term )
.

Definition subst_term_partial_solve_wit_4_pure := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) (y: Z) (var: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (list_Z_cmp (var) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  (store_string y var )
  **  (store_string src_pre src_str )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_term den_pre den_term )
|--
  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |]
.

Definition subst_term_partial_solve_wit_4_aux := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) (y: Z) (var: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (list_Z_cmp (var) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  (store_string y var )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_term den_pre den_term )
|--
  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = (list_Z_cmp (var) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string y var )
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
.

Definition subst_term_partial_solve_wit_4 := subst_term_partial_solve_wit_4_pure -> subst_term_partial_solve_wit_4_aux.

Definition subst_term_partial_solve_wit_5 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) (var: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (list_Z_cmp (var) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  (store_term t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| (retval = 0) |] 
  &&  [| (retval = (list_Z_cmp (var) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  (store_term t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
.

Definition subst_term_partial_solve_wit_6 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) (var: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (list_Z_cmp (var) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| (retval = 0) |] 
  &&  [| (retval = (list_Z_cmp (var) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermVar (var))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 = (termtypeID (trm))) |]
  &&  (store_term den_pre den_term )
  **  (store_string src_pre src_str )
.

Definition subst_term_partial_solve_wit_7_pure := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 = (termtypeID (trm))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| ((termtypeID (trm)) = 1) |] 
  &&  [| (t_pre <> 0) |]
.

Definition subst_term_partial_solve_wit_7_aux := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| ((termtypeID (trm)) = 1) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
.

Definition subst_term_partial_solve_wit_7 := subst_term_partial_solve_wit_7_pure -> subst_term_partial_solve_wit_7_aux.

Definition subst_term_partial_solve_wit_8_pure := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
.

Definition subst_term_partial_solve_wit_8_aux := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
.

Definition subst_term_partial_solve_wit_8 := subst_term_partial_solve_wit_8_pure -> subst_term_partial_solve_wit_8_aux.

Definition subst_term_partial_solve_wit_9_pure := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) (z: Z) (y: Z) (lt: term) (rt: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term y lt )
  **  (store_term z rt )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (y <> 0) |]
.

Definition subst_term_partial_solve_wit_9_aux := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) (z: Z) (y: Z) (lt: term) (rt: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term y lt )
  **  (store_term z rt )
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (y <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  (store_term y lt )
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term z rt )
.

Definition subst_term_partial_solve_wit_9 := subst_term_partial_solve_wit_9_pure -> subst_term_partial_solve_wit_9_aux.

Definition subst_term_partial_solve_wit_10_pure := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) (z: Z) (lt: term) (rt: term) (retval: Z) ,
  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  (store_term retval (term_subst_t (den_term) (src_str) (lt)) )
  **  (store_term den_pre den_term )
  **  (store_string src_pre src_str )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term z rt )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
|--
  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (z <> 0) |]
.

Definition subst_term_partial_solve_wit_10_aux := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) (z: Z) (lt: term) (rt: term) (retval: Z) ,
  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  (store_term retval (term_subst_t (den_term) (src_str) (lt)) )
  **  (store_term den_pre den_term )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term z rt )
|--
  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (z <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 = (termtypeID (trm))) |]
  &&  (store_term z rt )
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
  **  (store_term retval (term_subst_t (den_term) (src_str) (lt)) )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
.

Definition subst_term_partial_solve_wit_10 := subst_term_partial_solve_wit_10_pure -> subst_term_partial_solve_wit_10_aux.

Definition subst_term_partial_solve_wit_11_pure := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| ((termtypeID (trm)) = 3) |] 
  &&  [| (t_pre <> 0) |]
.

Definition subst_term_partial_solve_wit_11_aux := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| ((termtypeID (trm)) = 3) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
.

Definition subst_term_partial_solve_wit_11 := subst_term_partial_solve_wit_11_pure -> subst_term_partial_solve_wit_11_aux.

Definition subst_term_partial_solve_wit_12 := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) ,
  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
|--
  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |]
  &&  (store_string y qvar )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  (store_term den_pre den_term )
.

Definition subst_term_partial_solve_wit_13_pure := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) ,
  [| (retval = (list_Z_cmp (qvar) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |] 
  &&  [| (retval <> 0) |]
  &&  (store_string y qvar )
  **  (store_string src_pre src_str )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_term den_pre den_term )
|--
  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (z <> 0) |]
.

Definition subst_term_partial_solve_wit_13_aux := 
forall (t_pre: Z) (src_pre: Z) (den_pre: Z) (den_term: term) (src_str: (@list Z)) (trm: term) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) ,
  [| (retval = (list_Z_cmp (qvar) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |] 
  &&  [| (retval <> 0) |]
  &&  (store_string y qvar )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  (store_term den_pre den_term )
|--
  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (z <> 0) |] 
  &&  [| (retval = (list_Z_cmp (qvar) (src_str))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (trm = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (den_pre <> 0) |] 
  &&  [| (src_pre <> 0) |] 
  &&  [| (t_pre <> 0) |] 
  &&  [| (0 <> (termtypeID (trm))) |] 
  &&  [| (1 <> (termtypeID (trm))) |] 
  &&  [| (2 <> (termtypeID (trm))) |] 
  &&  [| (3 = (termtypeID (trm))) |] 
  &&  [| (retval <> 0) |]
  &&  (store_term z qterm )
  **  (store_string src_pre src_str )
  **  (store_term den_pre den_term )
  **  (store_string y qvar )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
.

Definition subst_term_partial_solve_wit_13 := subst_term_partial_solve_wit_13_pure -> subst_term_partial_solve_wit_13_aux.

Definition subst_term_which_implies_wit_1 := 
forall (trm: term) (t: Z) ,
  (store_term t trm )
|--
  [| (t <> 0) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
.

Definition subst_term_which_implies_wit_2 := 
forall (trm: term) (t: Z) ,
  [| ((termtypeID (trm)) = 0) |] 
  &&  [| (t <> 0) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
|--
  EX (y: Z)  (var: (@list Z)) ,
  [| (t <> 0) |] 
  &&  [| (trm = (TermVar (var))) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string y var )
.

Definition subst_term_which_implies_wit_3 := 
forall (trm: term) (var: (@list Z)) (y: Z) (t: Z) ,
  [| (t <> 0) |] 
  &&  [| (trm = (TermVar (var))) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string y var )
|--
  (store_term t trm )
.

Definition subst_term_which_implies_wit_4 := 
forall (trm: term) (t: Z) ,
  [| ((termtypeID (trm)) = 1) |] 
  &&  [| (t <> 0) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
|--
  EX (typ: const_type)  (con: Z) ,
  [| (t <> 0) |] 
  &&  [| (trm = (TermConst (typ) (con))) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con)
.

Definition subst_term_which_implies_wit_5 := 
forall (trm: term) (t: Z) ,
  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t <> 0) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
|--
  EX (z: Z)  (y: Z)  (lt: term)  (rt: term) ,
  [| (t <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term y lt )
  **  (store_term z rt )
.

Definition subst_term_which_implies_wit_6 := 
forall (trm: term) (t: Z) ,
  [| ((termtypeID (trm)) = 3) |] 
  &&  [| (t <> 0) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
|--
  EX (z: Z)  (y: Z)  (qt: quant_type)  (qvar: (@list Z))  (qterm: term) ,
  [| (t <> 0) |] 
  &&  [| (trm = (TermQuant (qt) (qvar) (qterm))) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include safeexec_Strategy_Correct.

Axiom proof_of_subst_var_safety_wit_1 : subst_var_safety_wit_1.
Axiom proof_of_subst_var_safety_wit_2 : subst_var_safety_wit_2.
Axiom proof_of_subst_var_safety_wit_3 : subst_var_safety_wit_3.
Axiom proof_of_subst_var_safety_wit_4 : subst_var_safety_wit_4.
Axiom proof_of_subst_var_safety_wit_5 : subst_var_safety_wit_5.
Axiom proof_of_subst_var_return_wit_1 : subst_var_return_wit_1.
Axiom proof_of_subst_var_return_wit_2 : subst_var_return_wit_2.
Axiom proof_of_subst_var_return_wit_3 : subst_var_return_wit_3.
Axiom proof_of_subst_var_return_wit_4 : subst_var_return_wit_4.
Axiom proof_of_subst_var_return_wit_5 : subst_var_return_wit_5.
Axiom proof_of_subst_var_return_wit_6 : subst_var_return_wit_6.
Axiom proof_of_subst_var_partial_solve_wit_1 : subst_var_partial_solve_wit_1.
Axiom proof_of_subst_var_partial_solve_wit_2_pure : subst_var_partial_solve_wit_2_pure.
Axiom proof_of_subst_var_partial_solve_wit_2 : subst_var_partial_solve_wit_2.
Axiom proof_of_subst_var_partial_solve_wit_3 : subst_var_partial_solve_wit_3.
Axiom proof_of_subst_var_partial_solve_wit_4_pure : subst_var_partial_solve_wit_4_pure.
Axiom proof_of_subst_var_partial_solve_wit_4 : subst_var_partial_solve_wit_4.
Axiom proof_of_subst_var_partial_solve_wit_5 : subst_var_partial_solve_wit_5.
Axiom proof_of_subst_var_partial_solve_wit_6_pure : subst_var_partial_solve_wit_6_pure.
Axiom proof_of_subst_var_partial_solve_wit_6 : subst_var_partial_solve_wit_6.
Axiom proof_of_subst_var_partial_solve_wit_7_pure : subst_var_partial_solve_wit_7_pure.
Axiom proof_of_subst_var_partial_solve_wit_7 : subst_var_partial_solve_wit_7.
Axiom proof_of_subst_var_partial_solve_wit_8_pure : subst_var_partial_solve_wit_8_pure.
Axiom proof_of_subst_var_partial_solve_wit_8 : subst_var_partial_solve_wit_8.
Axiom proof_of_subst_var_partial_solve_wit_9_pure : subst_var_partial_solve_wit_9_pure.
Axiom proof_of_subst_var_partial_solve_wit_9 : subst_var_partial_solve_wit_9.
Axiom proof_of_subst_var_partial_solve_wit_10_pure : subst_var_partial_solve_wit_10_pure.
Axiom proof_of_subst_var_partial_solve_wit_10 : subst_var_partial_solve_wit_10.
Axiom proof_of_subst_var_partial_solve_wit_11 : subst_var_partial_solve_wit_11.
Axiom proof_of_subst_var_partial_solve_wit_12_pure : subst_var_partial_solve_wit_12_pure.
Axiom proof_of_subst_var_partial_solve_wit_12 : subst_var_partial_solve_wit_12.
Axiom proof_of_subst_var_which_implies_wit_1 : subst_var_which_implies_wit_1.
Axiom proof_of_subst_var_which_implies_wit_2 : subst_var_which_implies_wit_2.
Axiom proof_of_subst_var_which_implies_wit_3 : subst_var_which_implies_wit_3.
Axiom proof_of_subst_var_which_implies_wit_4 : subst_var_which_implies_wit_4.
Axiom proof_of_subst_var_which_implies_wit_5 : subst_var_which_implies_wit_5.
Axiom proof_of_subst_term_safety_wit_1 : subst_term_safety_wit_1.
Axiom proof_of_subst_term_safety_wit_2 : subst_term_safety_wit_2.
Axiom proof_of_subst_term_safety_wit_3 : subst_term_safety_wit_3.
Axiom proof_of_subst_term_safety_wit_4 : subst_term_safety_wit_4.
Axiom proof_of_subst_term_safety_wit_5 : subst_term_safety_wit_5.
Axiom proof_of_subst_term_return_wit_1 : subst_term_return_wit_1.
Axiom proof_of_subst_term_return_wit_2 : subst_term_return_wit_2.
Axiom proof_of_subst_term_return_wit_3 : subst_term_return_wit_3.
Axiom proof_of_subst_term_return_wit_4 : subst_term_return_wit_4.
Axiom proof_of_subst_term_return_wit_5 : subst_term_return_wit_5.
Axiom proof_of_subst_term_return_wit_6 : subst_term_return_wit_6.
Axiom proof_of_subst_term_partial_solve_wit_1 : subst_term_partial_solve_wit_1.
Axiom proof_of_subst_term_partial_solve_wit_2_pure : subst_term_partial_solve_wit_2_pure.
Axiom proof_of_subst_term_partial_solve_wit_2 : subst_term_partial_solve_wit_2.
Axiom proof_of_subst_term_partial_solve_wit_3 : subst_term_partial_solve_wit_3.
Axiom proof_of_subst_term_partial_solve_wit_4_pure : subst_term_partial_solve_wit_4_pure.
Axiom proof_of_subst_term_partial_solve_wit_4 : subst_term_partial_solve_wit_4.
Axiom proof_of_subst_term_partial_solve_wit_5 : subst_term_partial_solve_wit_5.
Axiom proof_of_subst_term_partial_solve_wit_6 : subst_term_partial_solve_wit_6.
Axiom proof_of_subst_term_partial_solve_wit_7_pure : subst_term_partial_solve_wit_7_pure.
Axiom proof_of_subst_term_partial_solve_wit_7 : subst_term_partial_solve_wit_7.
Axiom proof_of_subst_term_partial_solve_wit_8_pure : subst_term_partial_solve_wit_8_pure.
Axiom proof_of_subst_term_partial_solve_wit_8 : subst_term_partial_solve_wit_8.
Axiom proof_of_subst_term_partial_solve_wit_9_pure : subst_term_partial_solve_wit_9_pure.
Axiom proof_of_subst_term_partial_solve_wit_9 : subst_term_partial_solve_wit_9.
Axiom proof_of_subst_term_partial_solve_wit_10_pure : subst_term_partial_solve_wit_10_pure.
Axiom proof_of_subst_term_partial_solve_wit_10 : subst_term_partial_solve_wit_10.
Axiom proof_of_subst_term_partial_solve_wit_11_pure : subst_term_partial_solve_wit_11_pure.
Axiom proof_of_subst_term_partial_solve_wit_11 : subst_term_partial_solve_wit_11.
Axiom proof_of_subst_term_partial_solve_wit_12 : subst_term_partial_solve_wit_12.
Axiom proof_of_subst_term_partial_solve_wit_13_pure : subst_term_partial_solve_wit_13_pure.
Axiom proof_of_subst_term_partial_solve_wit_13 : subst_term_partial_solve_wit_13.
Axiom proof_of_subst_term_which_implies_wit_1 : subst_term_which_implies_wit_1.
Axiom proof_of_subst_term_which_implies_wit_2 : subst_term_which_implies_wit_2.
Axiom proof_of_subst_term_which_implies_wit_3 : subst_term_which_implies_wit_3.
Axiom proof_of_subst_term_which_implies_wit_4 : subst_term_which_implies_wit_4.
Axiom proof_of_subst_term_which_implies_wit_5 : subst_term_which_implies_wit_5.
Axiom proof_of_subst_term_which_implies_wit_6 : subst_term_which_implies_wit_6.

End VC_Correct.

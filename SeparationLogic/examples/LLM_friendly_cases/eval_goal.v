Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_friendly_cases.eval_lib.
Local Open Scope sac.
From SimpleC.EE.LLM_friendly_cases Require Import eval_strategy_goal.
From SimpleC.EE.LLM_friendly_cases Require Import eval_strategy_proof.

(*----- Function eval -----*)

Definition eval_safety_wit_1 := 
forall (l: (@list Z)) (e0: expr) (var_value: Z) (e: Z) (e_t: Z) ,
  [| (safe_eval e0 l ) |]
  &&  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  (IntArray.full var_value 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e e_t e0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition eval_safety_wit_2 := 
forall (l: (@list Z)) (e0: expr) (var_value: Z) (e: Z) (e_t: Z) ,
  [| (safe_eval e0 l ) |] 
  &&  [| (0 <> e_t) |]
  &&  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  (IntArray.full var_value 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e e_t e0 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition eval_safety_wit_3 := 
forall (l: (@list Z)) (e0: expr) (var_value: Z) (e: Z) (e_t: Z) ,
  [| (safe_eval e0 l ) |] 
  &&  [| (0 <> e_t) |] 
  &&  [| (1 <> e_t) |]
  &&  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  (IntArray.full var_value 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e e_t e0 )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition eval_safety_wit_4 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) ,
  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
|--
  [| (11 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 11) |]
.

Definition eval_safety_wit_5 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition eval_safety_wit_6 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_2 = 0) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition eval_safety_wit_7 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) ,
  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (retval = 0) |]
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition eval_safety_wit_8 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) ,
  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
|--
  [| (12 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 12) |]
.

Definition eval_safety_wit_9 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) ,
  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (retval <> 0) |]
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition eval_safety_wit_10 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition eval_safety_wit_11 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 = 0) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition eval_safety_wit_12 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition eval_safety_wit_13 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| ((retval + retval_2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (retval + retval_2 )) |]
.

Definition eval_safety_wit_14 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition eval_safety_wit_15 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| ((retval - retval_2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (retval - retval_2 )) |]
.

Definition eval_safety_wit_16 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition eval_safety_wit_17 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| ((retval * retval_2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (retval * retval_2 )) |]
.

Definition eval_safety_wit_18 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition eval_safety_wit_19 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| ((retval <> (INT_MIN)) \/ (retval_2 <> (-1))) |] 
  &&  [| (retval_2 <> 0) |]
.

Definition eval_safety_wit_20 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition eval_safety_wit_21 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| ((retval <> (INT_MIN)) \/ (retval_2 <> (-1))) |] 
  &&  [| (retval_2 <> 0) |]
.

Definition eval_safety_wit_22 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 <> v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition eval_safety_wit_23 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 <> v) |] 
  &&  [| (5 <> v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition eval_safety_wit_24 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 <> v) |] 
  &&  [| (5 <> v) |] 
  &&  [| (6 <> v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (7 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 7) |]
.

Definition eval_safety_wit_25 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 <> v) |] 
  &&  [| (5 <> v) |] 
  &&  [| (6 <> v) |] 
  &&  [| (7 <> v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (8 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 8) |]
.

Definition eval_safety_wit_26 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 <> v) |] 
  &&  [| (5 <> v) |] 
  &&  [| (6 <> v) |] 
  &&  [| (7 <> v) |] 
  &&  [| (8 <> v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (9 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 9) |]
.

Definition eval_safety_wit_27 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 <> v) |] 
  &&  [| (5 <> v) |] 
  &&  [| (6 <> v) |] 
  &&  [| (7 <> v) |] 
  &&  [| (8 <> v) |] 
  &&  [| (9 <> v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition eval_safety_wit_28 := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 <> v) |] 
  &&  [| (5 <> v) |] 
  &&  [| (6 <> v) |] 
  &&  [| (7 <> v) |] 
  &&  [| (8 <> v) |] 
  &&  [| (9 <> v) |] 
  &&  [| (10 <> v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "right_val" ) )) # Int  |-> retval_2)
  **  (store_expr v_2 e1 )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| False |]
.

Definition eval_safety_wit_29 := 
forall (l: (@list Z)) (e0: expr) (var_value: Z) (e: Z) (e_t: Z) ,
  [| (safe_eval e0 l ) |] 
  &&  [| (0 <> e_t) |] 
  &&  [| (1 <> e_t) |] 
  &&  [| (2 <> e_t) |]
  &&  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  (IntArray.full var_value 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e e_t e0 )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition eval_safety_wit_30 := 
forall (l: (@list Z)) (e0: expr) (op: unop) (e1: expr) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) ,
  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v = (UnOpID (op))) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition eval_safety_wit_31 := 
forall (l: (@list Z)) (e0: expr) (op: unop) (e1: expr) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (retval: Z) ,
  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 1) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v = (UnOpID (op))) |]
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v_2)
|--
  [| (retval <> (INT_MIN)) |]
.

Definition eval_safety_wit_32 := 
forall (l: (@list Z)) (e0: expr) (var_value: Z) (e: Z) (e_t: Z) ,
  [| (safe_eval e0 l ) |] 
  &&  [| (0 <> e_t) |] 
  &&  [| (1 <> e_t) |] 
  &&  [| (2 <> e_t) |] 
  &&  [| (3 <> e_t) |]
  &&  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  (IntArray.full var_value 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e e_t e0 )
|--
  [| False |]
.

Definition eval_entail_wit_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) ,
  [| (safe_eval e0 l ) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
|--
  EX (e_t: Z) ,
  [| (safe_eval e0 l ) |]
  &&  (IntArray.full var_value_pre 100 l )
  **  ((&((e_pre)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  (store_expr_aux e_pre e_t e0 )
.

Definition eval_entail_wit_2 := 
forall (l: (@list Z)) (e0: expr) (var_value: Z) (e: Z) (e_t_2: Z) ,
  [| (safe_eval e0 l ) |] 
  &&  [| (0 = e_t_2) |]
  &&  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t_2)
  **  (store_expr_aux e e_t_2 e0 )
|--
  EX (n: Z)  (e_t: Z) ,
  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 0) |] 
  &&  [| (e0 = (EConst (n))) |]
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "CONST" .ₛ "value")) # Int  |-> n)
  **  (IntArray.full var_value 100 l )
  **  (store_expr_aux e e_t e0 )
.

Definition eval_entail_wit_3 := 
forall (l: (@list Z)) (e0: expr) (var_value: Z) (e: Z) (e_t_2: Z) ,
  [| (safe_eval e0 l ) |] 
  &&  [| (0 <> e_t_2) |] 
  &&  [| (1 = e_t_2) |]
  &&  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t_2)
  **  (store_expr_aux e e_t_2 e0 )
|--
  EX (e_t: Z)  (n: Z) ,
  [| (safe_eval e0 l ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (e_t = 1) |] 
  &&  [| (e0 = (EVar (n))) |]
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (IntArray.full var_value 100 l )
  **  (store_expr_aux e e_t e0 )
.

Definition eval_entail_wit_4 := 
forall (l: (@list Z)) (e0: expr) (var_value: Z) (e: Z) (e_t_2: Z) ,
  [| (safe_eval e0 l ) |] 
  &&  [| (0 <> e_t_2) |] 
  &&  [| (1 <> e_t_2) |] 
  &&  [| (2 = e_t_2) |]
  &&  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t_2)
  **  (store_expr_aux e e_t_2 e0 )
|--
  EX (v_3: Z)  (v_2: Z)  (v: Z)  (op: binop)  (e1: expr)  (e2: expr)  (e_t: Z) ,
  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |]
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
.

Definition eval_entail_wit_5 := 
forall (l: (@list Z)) (e0: expr) (var_value: Z) (e: Z) (e_t_2: Z) ,
  [| (safe_eval e0 l ) |] 
  &&  [| (0 <> e_t_2) |] 
  &&  [| (1 <> e_t_2) |] 
  &&  [| (2 <> e_t_2) |] 
  &&  [| (3 = e_t_2) |]
  &&  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t_2)
  **  (store_expr_aux e e_t_2 e0 )
|--
  EX (v_2: Z)  (v: Z)  (op: unop)  (e1: expr)  (e_t: Z) ,
  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v = (UnOpID (op))) |]
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v)
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
.

Definition eval_return_wit_1 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (op: unop) (e1: expr) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (retval: Z) ,
  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 1) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v = (UnOpID (op))) |]
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v_2)
|--
  [| ((-retval) = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_2 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (op: unop) (e1: expr) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 1) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v = (UnOpID (op))) |]
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v_2)
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_3 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (op: unop) (e1: expr) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 1) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v = (UnOpID (op))) |]
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v_2)
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_4 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval <> retval_2) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 <> v) |] 
  &&  [| (5 <> v) |] 
  &&  [| (6 <> v) |] 
  &&  [| (7 <> v) |] 
  &&  [| (8 <> v) |] 
  &&  [| (9 <> v) |] 
  &&  [| (10 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_5 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval = retval_2) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 <> v) |] 
  &&  [| (5 <> v) |] 
  &&  [| (6 <> v) |] 
  &&  [| (7 <> v) |] 
  &&  [| (8 <> v) |] 
  &&  [| (9 <> v) |] 
  &&  [| (10 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_6 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval = retval_2) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 <> v) |] 
  &&  [| (5 <> v) |] 
  &&  [| (6 <> v) |] 
  &&  [| (7 <> v) |] 
  &&  [| (8 <> v) |] 
  &&  [| (9 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_7 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval <> retval_2) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 <> v) |] 
  &&  [| (5 <> v) |] 
  &&  [| (6 <> v) |] 
  &&  [| (7 <> v) |] 
  &&  [| (8 <> v) |] 
  &&  [| (9 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_8 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval >= retval_2) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 <> v) |] 
  &&  [| (5 <> v) |] 
  &&  [| (6 <> v) |] 
  &&  [| (7 <> v) |] 
  &&  [| (8 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_9 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval < retval_2) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 <> v) |] 
  &&  [| (5 <> v) |] 
  &&  [| (6 <> v) |] 
  &&  [| (7 <> v) |] 
  &&  [| (8 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_10 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval <= retval_2) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 <> v) |] 
  &&  [| (5 <> v) |] 
  &&  [| (6 <> v) |] 
  &&  [| (7 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_11 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval > retval_2) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 <> v) |] 
  &&  [| (5 <> v) |] 
  &&  [| (6 <> v) |] 
  &&  [| (7 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_12 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval > retval_2) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 <> v) |] 
  &&  [| (5 <> v) |] 
  &&  [| (6 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_13 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval <= retval_2) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 <> v) |] 
  &&  [| (5 <> v) |] 
  &&  [| (6 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_14 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval < retval_2) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 <> v) |] 
  &&  [| (5 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_15 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval >= retval_2) |] 
  &&  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 <> v) |] 
  &&  [| (5 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_16 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 <> v) |] 
  &&  [| (4 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| ((retval % ( retval_2 ) ) = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_17 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 <> v) |] 
  &&  [| (3 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| ((retval ÷ retval_2 ) = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_18 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 <> v) |] 
  &&  [| (2 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| ((retval * retval_2 ) = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_19 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 <> v) |] 
  &&  [| (1 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| ((retval - retval_2 ) = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_20 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (0 = v) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| ((retval + retval_2 ) = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_21 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 = 0) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_22 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_23 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) ,
  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (retval <> 0) |]
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_24 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) ,
  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (retval = 0) |]
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_25 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_2 = 0) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (0 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_26 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = (expr_eval (e2) (l))) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
|--
  [| (1 = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_27 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (n: Z) (e: Z) (e_t: Z) (var_value: Z) ,
  [| (safe_eval e0 l ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (e_t = 1) |] 
  &&  [| (e0 = (EVar (n))) |]
  &&  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_expr_aux e e_t e0 )
|--
  [| ((Znth n l 0) = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_return_wit_28 := 
forall (var_value_pre: Z) (e_pre: Z) (l: (@list Z)) (e0: expr) (n: Z) (e: Z) (e_t: Z) (var_value: Z) ,
  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 0) |] 
  &&  [| (e0 = (EConst (n))) |]
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "CONST" .ₛ "value")) # Int  |-> n)
  **  (IntArray.full var_value 100 l )
  **  (store_expr_aux e e_t e0 )
|--
  [| (n = (expr_eval (e0) (l))) |]
  &&  (store_expr e_pre e0 )
  **  (IntArray.full var_value_pre 100 l )
.

Definition eval_partial_solve_wit_1 := 
forall (l: (@list Z)) (e0: expr) (n: Z) (e: Z) (e_t: Z) (var_value: Z) ,
  [| (safe_eval e0 l ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (e_t = 1) |] 
  &&  [| (e0 = (EVar (n))) |]
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (IntArray.full var_value 100 l )
  **  (store_expr_aux e e_t e0 )
|--
  [| (safe_eval e0 l ) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < 100) |] 
  &&  [| (e_t = 1) |] 
  &&  [| (e0 = (EVar (n))) |]
  &&  (((var_value + (n * sizeof(INT) ) )) # Int  |-> (Znth n l 0))
  **  (IntArray.missing_i var_value n 0 100 l )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_expr_aux e e_t e0 )
.

Definition eval_partial_solve_wit_2_pure := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) ,
  [| (v = 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
|--
  [| (safe_eval e1 l ) |]
.

Definition eval_partial_solve_wit_2_aux := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) ,
  [| (v = 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |]
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
|--
  [| (safe_eval e1 l ) |] 
  &&  [| (v = 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |]
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
.

Definition eval_partial_solve_wit_2 := eval_partial_solve_wit_2_pure -> eval_partial_solve_wit_2_aux.

Definition eval_partial_solve_wit_3_pure := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) ,
  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (retval <> 0) |]
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
|--
  [| (safe_eval e2 l ) |]
.

Definition eval_partial_solve_wit_3_aux := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) ,
  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (retval <> 0) |]
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
|--
  [| (safe_eval e2 l ) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (retval <> 0) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
.

Definition eval_partial_solve_wit_3 := eval_partial_solve_wit_3_pure -> eval_partial_solve_wit_3_aux.

Definition eval_partial_solve_wit_4_pure := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) ,
  [| (v = 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
|--
  [| (safe_eval e1 l ) |]
.

Definition eval_partial_solve_wit_4_aux := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) ,
  [| (v = 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |]
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
|--
  [| (safe_eval e1 l ) |] 
  &&  [| (v = 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |]
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
.

Definition eval_partial_solve_wit_4 := eval_partial_solve_wit_4_pure -> eval_partial_solve_wit_4_aux.

Definition eval_partial_solve_wit_5_pure := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) ,
  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (retval = 0) |]
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
|--
  [| (safe_eval e2 l ) |]
.

Definition eval_partial_solve_wit_5_aux := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) ,
  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (retval = 0) |]
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
|--
  [| (safe_eval e2 l ) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v = 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |] 
  &&  [| (retval = 0) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
.

Definition eval_partial_solve_wit_5 := eval_partial_solve_wit_5_pure -> eval_partial_solve_wit_5_aux.

Definition eval_partial_solve_wit_6_pure := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) ,
  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |]
  &&  ((( &( "left_val" ) )) # Int  |->_)
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
|--
  [| (safe_eval e1 l ) |]
.

Definition eval_partial_solve_wit_6_aux := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) ,
  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |]
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
|--
  [| (safe_eval e1 l ) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |]
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
.

Definition eval_partial_solve_wit_6 := eval_partial_solve_wit_6_pure -> eval_partial_solve_wit_6_aux.

Definition eval_partial_solve_wit_7_pure := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) ,
  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |]
  &&  ((( &( "right_val" ) )) # Int  |->_)
  **  (store_expr v_2 e1 )
  **  (IntArray.full var_value 100 l )
  **  ((( &( "left_val" ) )) # Int  |-> retval)
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
|--
  [| (safe_eval e2 l ) |]
.

Definition eval_partial_solve_wit_7_aux := 
forall (l: (@list Z)) (e0: expr) (e1: expr) (e2: expr) (op: binop) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) (v_3: Z) (retval: Z) ,
  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |]
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_expr v_3 e2 )
|--
  [| (safe_eval e2 l ) |] 
  &&  [| (retval = (expr_eval (e1) (l))) |] 
  &&  [| (v <> 12) |] 
  &&  [| (v <> 11) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 2) |] 
  &&  [| (e0 = (EBinop (op) (e1) (e2))) |] 
  &&  [| (v = (BinOpID (op))) |]
  &&  (store_expr v_3 e2 )
  **  (IntArray.full var_value 100 l )
  **  (store_expr v_2 e1 )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right")) # Ptr  |-> v_3)
.

Definition eval_partial_solve_wit_7 := eval_partial_solve_wit_7_pure -> eval_partial_solve_wit_7_aux.

Definition eval_partial_solve_wit_8_pure := 
forall (l: (@list Z)) (e0: expr) (op: unop) (e1: expr) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) ,
  [| (v = 1) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v = (UnOpID (op))) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
|--
  [| (safe_eval e1 l ) |]
.

Definition eval_partial_solve_wit_8_aux := 
forall (l: (@list Z)) (e0: expr) (op: unop) (e1: expr) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) ,
  [| (v = 1) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v = (UnOpID (op))) |]
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v)
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
|--
  [| (safe_eval e1 l ) |] 
  &&  [| (v = 1) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v = (UnOpID (op))) |]
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v_2)
.

Definition eval_partial_solve_wit_8 := eval_partial_solve_wit_8_pure -> eval_partial_solve_wit_8_aux.

Definition eval_partial_solve_wit_9_pure := 
forall (l: (@list Z)) (e0: expr) (op: unop) (e1: expr) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) ,
  [| (v <> 1) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v = (UnOpID (op))) |]
  &&  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v)
  **  ((( &( "var_value" ) )) # Ptr  |-> var_value)
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
|--
  [| (safe_eval e1 l ) |]
.

Definition eval_partial_solve_wit_9_aux := 
forall (l: (@list Z)) (e0: expr) (op: unop) (e1: expr) (e: Z) (e_t: Z) (v: Z) (var_value: Z) (v_2: Z) ,
  [| (v <> 1) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v = (UnOpID (op))) |]
  &&  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v)
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v_2)
  **  (store_expr v_2 e1 )
|--
  [| (safe_eval e1 l ) |] 
  &&  [| (v <> 1) |] 
  &&  [| (safe_eval e0 l ) |] 
  &&  [| (e_t = 3) |] 
  &&  [| (e0 = (EUnop (op) (e1))) |] 
  &&  [| (v = (UnOpID (op))) |]
  &&  (store_expr v_2 e1 )
  **  (IntArray.full var_value 100 l )
  **  ((&((e)  # "expr" ->ₛ "t")) # Int  |-> e_t)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op")) # Int  |-> v)
  **  ((&((e)  # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg")) # Ptr  |-> v_2)
.

Definition eval_partial_solve_wit_9 := eval_partial_solve_wit_9_pure -> eval_partial_solve_wit_9_aux.

Module Type VC_Correct.

Include eval_Strategy_Correct.

Axiom proof_of_eval_safety_wit_1 : eval_safety_wit_1.
Axiom proof_of_eval_safety_wit_2 : eval_safety_wit_2.
Axiom proof_of_eval_safety_wit_3 : eval_safety_wit_3.
Axiom proof_of_eval_safety_wit_4 : eval_safety_wit_4.
Axiom proof_of_eval_safety_wit_5 : eval_safety_wit_5.
Axiom proof_of_eval_safety_wit_6 : eval_safety_wit_6.
Axiom proof_of_eval_safety_wit_7 : eval_safety_wit_7.
Axiom proof_of_eval_safety_wit_8 : eval_safety_wit_8.
Axiom proof_of_eval_safety_wit_9 : eval_safety_wit_9.
Axiom proof_of_eval_safety_wit_10 : eval_safety_wit_10.
Axiom proof_of_eval_safety_wit_11 : eval_safety_wit_11.
Axiom proof_of_eval_safety_wit_12 : eval_safety_wit_12.
Axiom proof_of_eval_safety_wit_13 : eval_safety_wit_13.
Axiom proof_of_eval_safety_wit_14 : eval_safety_wit_14.
Axiom proof_of_eval_safety_wit_15 : eval_safety_wit_15.
Axiom proof_of_eval_safety_wit_16 : eval_safety_wit_16.
Axiom proof_of_eval_safety_wit_17 : eval_safety_wit_17.
Axiom proof_of_eval_safety_wit_18 : eval_safety_wit_18.
Axiom proof_of_eval_safety_wit_19 : eval_safety_wit_19.
Axiom proof_of_eval_safety_wit_20 : eval_safety_wit_20.
Axiom proof_of_eval_safety_wit_21 : eval_safety_wit_21.
Axiom proof_of_eval_safety_wit_22 : eval_safety_wit_22.
Axiom proof_of_eval_safety_wit_23 : eval_safety_wit_23.
Axiom proof_of_eval_safety_wit_24 : eval_safety_wit_24.
Axiom proof_of_eval_safety_wit_25 : eval_safety_wit_25.
Axiom proof_of_eval_safety_wit_26 : eval_safety_wit_26.
Axiom proof_of_eval_safety_wit_27 : eval_safety_wit_27.
Axiom proof_of_eval_safety_wit_28 : eval_safety_wit_28.
Axiom proof_of_eval_safety_wit_29 : eval_safety_wit_29.
Axiom proof_of_eval_safety_wit_30 : eval_safety_wit_30.
Axiom proof_of_eval_safety_wit_31 : eval_safety_wit_31.
Axiom proof_of_eval_safety_wit_32 : eval_safety_wit_32.
Axiom proof_of_eval_entail_wit_1 : eval_entail_wit_1.
Axiom proof_of_eval_entail_wit_2 : eval_entail_wit_2.
Axiom proof_of_eval_entail_wit_3 : eval_entail_wit_3.
Axiom proof_of_eval_entail_wit_4 : eval_entail_wit_4.
Axiom proof_of_eval_entail_wit_5 : eval_entail_wit_5.
Axiom proof_of_eval_return_wit_1 : eval_return_wit_1.
Axiom proof_of_eval_return_wit_2 : eval_return_wit_2.
Axiom proof_of_eval_return_wit_3 : eval_return_wit_3.
Axiom proof_of_eval_return_wit_4 : eval_return_wit_4.
Axiom proof_of_eval_return_wit_5 : eval_return_wit_5.
Axiom proof_of_eval_return_wit_6 : eval_return_wit_6.
Axiom proof_of_eval_return_wit_7 : eval_return_wit_7.
Axiom proof_of_eval_return_wit_8 : eval_return_wit_8.
Axiom proof_of_eval_return_wit_9 : eval_return_wit_9.
Axiom proof_of_eval_return_wit_10 : eval_return_wit_10.
Axiom proof_of_eval_return_wit_11 : eval_return_wit_11.
Axiom proof_of_eval_return_wit_12 : eval_return_wit_12.
Axiom proof_of_eval_return_wit_13 : eval_return_wit_13.
Axiom proof_of_eval_return_wit_14 : eval_return_wit_14.
Axiom proof_of_eval_return_wit_15 : eval_return_wit_15.
Axiom proof_of_eval_return_wit_16 : eval_return_wit_16.
Axiom proof_of_eval_return_wit_17 : eval_return_wit_17.
Axiom proof_of_eval_return_wit_18 : eval_return_wit_18.
Axiom proof_of_eval_return_wit_19 : eval_return_wit_19.
Axiom proof_of_eval_return_wit_20 : eval_return_wit_20.
Axiom proof_of_eval_return_wit_21 : eval_return_wit_21.
Axiom proof_of_eval_return_wit_22 : eval_return_wit_22.
Axiom proof_of_eval_return_wit_23 : eval_return_wit_23.
Axiom proof_of_eval_return_wit_24 : eval_return_wit_24.
Axiom proof_of_eval_return_wit_25 : eval_return_wit_25.
Axiom proof_of_eval_return_wit_26 : eval_return_wit_26.
Axiom proof_of_eval_return_wit_27 : eval_return_wit_27.
Axiom proof_of_eval_return_wit_28 : eval_return_wit_28.
Axiom proof_of_eval_partial_solve_wit_1 : eval_partial_solve_wit_1.
Axiom proof_of_eval_partial_solve_wit_2_pure : eval_partial_solve_wit_2_pure.
Axiom proof_of_eval_partial_solve_wit_2 : eval_partial_solve_wit_2.
Axiom proof_of_eval_partial_solve_wit_3_pure : eval_partial_solve_wit_3_pure.
Axiom proof_of_eval_partial_solve_wit_3 : eval_partial_solve_wit_3.
Axiom proof_of_eval_partial_solve_wit_4_pure : eval_partial_solve_wit_4_pure.
Axiom proof_of_eval_partial_solve_wit_4 : eval_partial_solve_wit_4.
Axiom proof_of_eval_partial_solve_wit_5_pure : eval_partial_solve_wit_5_pure.
Axiom proof_of_eval_partial_solve_wit_5 : eval_partial_solve_wit_5.
Axiom proof_of_eval_partial_solve_wit_6_pure : eval_partial_solve_wit_6_pure.
Axiom proof_of_eval_partial_solve_wit_6 : eval_partial_solve_wit_6.
Axiom proof_of_eval_partial_solve_wit_7_pure : eval_partial_solve_wit_7_pure.
Axiom proof_of_eval_partial_solve_wit_7 : eval_partial_solve_wit_7.
Axiom proof_of_eval_partial_solve_wit_8_pure : eval_partial_solve_wit_8_pure.
Axiom proof_of_eval_partial_solve_wit_8 : eval_partial_solve_wit_8.
Axiom proof_of_eval_partial_solve_wit_9_pure : eval_partial_solve_wit_9_pure.
Axiom proof_of_eval_partial_solve_wit_9 : eval_partial_solve_wit_9.

End VC_Correct.

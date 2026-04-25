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
Require Import coins_106.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function f -----*)

Definition f_safety_wit_1 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (n_pre = n0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |]
  &&  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 n_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition f_safety_wit_2 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (n_pre = n0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |]
  &&  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 n_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition f_safety_wit_3 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (n_pre = n0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 n_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition f_safety_wit_4 := 
forall (n0: Z) (p: Z) (s: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 i (sublist (0) (i) ((f_seq (n0)))) )
  **  (IntArray.undef_seg data i n0 )
|--
  [| ((s + (i + 1 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (s + (i + 1 ) )) |]
.

Definition f_safety_wit_5 := 
forall (n0: Z) (p: Z) (s: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 i (sublist (0) (i) ((f_seq (n0)))) )
  **  (IntArray.undef_seg data i n0 )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition f_safety_wit_6 := 
forall (n0: Z) (p: Z) (s: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 i (sublist (0) (i) ((f_seq (n0)))) )
  **  (IntArray.undef_seg data i n0 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition f_safety_wit_7 := 
forall (n0: Z) (p: Z) (s: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> (s + (i + 1 ) ))
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 i (sublist (0) (i) ((f_seq (n0)))) )
  **  (IntArray.undef_seg data i n0 )
|--
  [| ((p * (i + 1 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (p * (i + 1 ) )) |]
.

Definition f_safety_wit_8 := 
forall (n0: Z) (p: Z) (s: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> (s + (i + 1 ) ))
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 i (sublist (0) (i) ((f_seq (n0)))) )
  **  (IntArray.undef_seg data i n0 )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition f_safety_wit_9 := 
forall (n0: Z) (p: Z) (s: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> (s + (i + 1 ) ))
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 i (sublist (0) (i) ((f_seq (n0)))) )
  **  (IntArray.undef_seg data i n0 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition f_safety_wit_10 := 
forall (n0: Z) (p: Z) (s: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> (s + (i + 1 ) ))
  **  ((( &( "p" ) )) # Int  |-> (p * (i + 1 ) ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 i (sublist (0) (i) ((f_seq (n0)))) )
  **  (IntArray.undef_seg data i n0 )
|--
  [| (((i + 1 ) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition f_safety_wit_11 := 
forall (n0: Z) (p: Z) (s: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> (s + (i + 1 ) ))
  **  ((( &( "p" ) )) # Int  |-> (p * (i + 1 ) ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 i (sublist (0) (i) ((f_seq (n0)))) )
  **  (IntArray.undef_seg data i n0 )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition f_safety_wit_12 := 
forall (n0: Z) (p: Z) (s: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> (s + (i + 1 ) ))
  **  ((( &( "p" ) )) # Int  |-> (p * (i + 1 ) ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 i (sublist (0) (i) ((f_seq (n0)))) )
  **  (IntArray.undef_seg data i n0 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition f_safety_wit_13 := 
forall (n0: Z) (p: Z) (s: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> (s + (i + 1 ) ))
  **  ((( &( "p" ) )) # Int  |-> (p * (i + 1 ) ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 i (sublist (0) (i) ((f_seq (n0)))) )
  **  (IntArray.undef_seg data i n0 )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition f_safety_wit_14 := 
forall (n0: Z) (p: Z) (s: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> (s + (i + 1 ) ))
  **  ((( &( "p" ) )) # Int  |-> (p * (i + 1 ) ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 i (sublist (0) (i) ((f_seq (n0)))) )
  **  (IntArray.undef_seg data i n0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition f_safety_wit_15 := 
forall (n0: Z) (p: Z) (s: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((i + 1 ) % ( 2 ) ) <> 0) |] 
  &&  [| (i < n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (s + (i + 1 ) ))
  **  (IntArray.undef_seg data (i + 1 ) n0 )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> (s + (i + 1 ) ))
  **  ((( &( "p" ) )) # Int  |-> (p * (i + 1 ) ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 i (sublist (0) (i) ((f_seq (n0)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition f_safety_wit_16 := 
forall (n0: Z) (p: Z) (s: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((i + 1 ) % ( 2 ) ) = 0) |] 
  &&  [| (i < n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (p * (i + 1 ) ))
  **  (IntArray.undef_seg data (i + 1 ) n0 )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> (s + (i + 1 ) ))
  **  ((( &( "p" ) )) # Int  |-> (p * (i + 1 ) ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 i (sublist (0) (i) ((f_seq (n0)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition f_entail_wit_1 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (n_pre = n0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |]
  &&  (IntArray.undef_full retval_2 n_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (0 = (triangular_z (0))) |] 
  &&  [| (1 = (factorial_z (0))) |]
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg retval_2 0 0 (sublist (0) (0) ((f_seq (n0)))) )
  **  (IntArray.undef_seg retval_2 0 n0 )
.

Definition f_entail_wit_2_1 := 
forall (n0: Z) (p: Z) (s: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((i + 1 ) % ( 2 ) ) = 0) |] 
  &&  [| (i < n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (p * (i + 1 ) ))
  **  (IntArray.undef_seg data (i + 1 ) n0 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 i (sublist (0) (i) ((f_seq (n0)))) )
|--
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| ((s + (i + 1 ) ) = (triangular_z ((i + 1 )))) |] 
  &&  [| ((p * (i + 1 ) ) = (factorial_z ((i + 1 )))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 (i + 1 ) (sublist (0) ((i + 1 )) ((f_seq (n0)))) )
  **  (IntArray.undef_seg data (i + 1 ) n0 )
.

Definition f_entail_wit_2_2 := 
forall (n0: Z) (p: Z) (s: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((i + 1 ) % ( 2 ) ) <> 0) |] 
  &&  [| (i < n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> (s + (i + 1 ) ))
  **  (IntArray.undef_seg data (i + 1 ) n0 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 i (sublist (0) (i) ((f_seq (n0)))) )
|--
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| ((s + (i + 1 ) ) = (triangular_z ((i + 1 )))) |] 
  &&  [| ((p * (i + 1 ) ) = (factorial_z ((i + 1 )))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 (i + 1 ) (sublist (0) ((i + 1 )) ((f_seq (n0)))) )
  **  (IntArray.undef_seg data (i + 1 ) n0 )
.

Definition f_return_wit_1 := 
forall (n0: Z) (p: Z) (s: Z) (i: Z) (data_2: Z) (out: Z) ,
  [| (i >= n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data_2 0 i (sublist (0) (i) ((f_seq (n0)))) )
  **  (IntArray.undef_seg data_2 i n0 )
|--
  EX (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (output_size = n0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (f_seq (n0))) |] 
  &&  [| (problem_106_spec_z n0 output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full data output_size output_l )
.

Definition f_partial_solve_wit_1 := 
forall (n_pre: Z) (n0: Z) ,
  [| (n_pre = n0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |]
  &&  emp
|--
  [| (n_pre = n0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |]
  &&  emp
.

Definition f_partial_solve_wit_2_pure := 
forall (n_pre: Z) (n0: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (n_pre = n0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (n_pre >= 0) |] 
  &&  [| (n_pre < INT_MAX) |]
.

Definition f_partial_solve_wit_2_aux := 
forall (n_pre: Z) (n0: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (n_pre = n0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n_pre)
|--
  [| (n_pre >= 0) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (n_pre = n0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n_pre)
.

Definition f_partial_solve_wit_2 := f_partial_solve_wit_2_pure -> f_partial_solve_wit_2_aux.

Definition f_partial_solve_wit_3 := 
forall (n0: Z) (p: Z) (s: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((i + 1 ) % ( 2 ) ) = 0) |] 
  &&  [| (i < n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 i (sublist (0) (i) ((f_seq (n0)))) )
  **  (IntArray.undef_seg data i n0 )
|--
  [| (((i + 1 ) % ( 2 ) ) = 0) |] 
  &&  [| (i < n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (i + 1 ) n0 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 i (sublist (0) (i) ((f_seq (n0)))) )
.

Definition f_partial_solve_wit_4 := 
forall (n0: Z) (p: Z) (s: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((i + 1 ) % ( 2 ) ) <> 0) |] 
  &&  [| (i < n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 i (sublist (0) (i) ((f_seq (n0)))) )
  **  (IntArray.undef_seg data i n0 )
|--
  [| (((i + 1 ) % ( 2 ) ) <> 0) |] 
  &&  [| (i < n0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (1 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (problem_106_pre_z n0 ) |] 
  &&  [| (f_seq_int_range n0 ) |] 
  &&  [| ((Zlength ((f_seq (n0)))) = n0) |] 
  &&  [| (s = (triangular_z (i))) |] 
  &&  [| (p = (factorial_z (i))) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (i + 1 ) n0 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0)
  **  (IntArray.seg data 0 i (sublist (0) (i) ((f_seq (n0)))) )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_f_safety_wit_1 : f_safety_wit_1.
Axiom proof_of_f_safety_wit_2 : f_safety_wit_2.
Axiom proof_of_f_safety_wit_3 : f_safety_wit_3.
Axiom proof_of_f_safety_wit_4 : f_safety_wit_4.
Axiom proof_of_f_safety_wit_5 : f_safety_wit_5.
Axiom proof_of_f_safety_wit_6 : f_safety_wit_6.
Axiom proof_of_f_safety_wit_7 : f_safety_wit_7.
Axiom proof_of_f_safety_wit_8 : f_safety_wit_8.
Axiom proof_of_f_safety_wit_9 : f_safety_wit_9.
Axiom proof_of_f_safety_wit_10 : f_safety_wit_10.
Axiom proof_of_f_safety_wit_11 : f_safety_wit_11.
Axiom proof_of_f_safety_wit_12 : f_safety_wit_12.
Axiom proof_of_f_safety_wit_13 : f_safety_wit_13.
Axiom proof_of_f_safety_wit_14 : f_safety_wit_14.
Axiom proof_of_f_safety_wit_15 : f_safety_wit_15.
Axiom proof_of_f_safety_wit_16 : f_safety_wit_16.
Axiom proof_of_f_entail_wit_1 : f_entail_wit_1.
Axiom proof_of_f_entail_wit_2_1 : f_entail_wit_2_1.
Axiom proof_of_f_entail_wit_2_2 : f_entail_wit_2_2.
Axiom proof_of_f_return_wit_1 : f_return_wit_1.
Axiom proof_of_f_partial_solve_wit_1 : f_partial_solve_wit_1.
Axiom proof_of_f_partial_solve_wit_2_pure : f_partial_solve_wit_2_pure.
Axiom proof_of_f_partial_solve_wit_2 : f_partial_solve_wit_2.
Axiom proof_of_f_partial_solve_wit_3 : f_partial_solve_wit_3.
Axiom proof_of_f_partial_solve_wit_4 : f_partial_solve_wit_4.

End VC_Correct.

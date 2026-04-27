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
Require Import coins_121.
Local Open Scope sac.
From SimpleC.EE Require Import int_array_strategy_goal.
From SimpleC.EE Require Import int_array_strategy_proof.
From SimpleC.EE Require Import uint_array_strategy_goal.
From SimpleC.EE Require Import uint_array_strategy_proof.
From SimpleC.EE Require Import undef_uint_array_strategy_goal.
From SimpleC.EE Require Import undef_uint_array_strategy_proof.
From SimpleC.EE Require Import array_shape_strategy_goal.
From SimpleC.EE Require Import array_shape_strategy_proof.

(*----- Function solutions -----*)

Definition solutions_safety_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) ,
  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |]
  &&  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solutions_safety_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) ,
  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Int  |-> 0)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solutions_safety_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto (i) (lv))) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| ((i * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i * 2 )) |]
.

Definition solutions_safety_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto (i) (lv))) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition solutions_safety_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((i * 2 ) < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto (i) (lv))) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
|--
  [| (((Znth (i * 2 ) lv 0) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition solutions_safety_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((i * 2 ) < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto (i) (lv))) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| ((i * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i * 2 )) |]
.

Definition solutions_safety_wit_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((i * 2 ) < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto (i) (lv))) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition solutions_safety_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((i * 2 ) < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto (i) (lv))) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition solutions_safety_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((i * 2 ) < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto (i) (lv))) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition solutions_safety_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (((Znth (i * 2 ) lv 0) % ( 2 ) ) = 1) |] 
  &&  [| ((i * 2 ) < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto (i) (lv))) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
|--
  [| ((s + (Znth (i * 2 ) lv 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (s + (Znth (i * 2 ) lv 0) )) |]
.

Definition solutions_safety_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (((Znth (i * 2 ) lv 0) % ( 2 ) ) = 1) |] 
  &&  [| ((i * 2 ) < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto (i) (lv))) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
|--
  [| ((i * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i * 2 )) |]
.

Definition solutions_safety_wit_12 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (((Znth (i * 2 ) lv 0) % ( 2 ) ) = 1) |] 
  &&  [| ((i * 2 ) < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto (i) (lv))) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition solutions_safety_wit_13 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (((Znth (i * 2 ) lv 0) % ( 2 ) ) <> 1) |] 
  &&  [| ((i * 2 ) < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto (i) (lv))) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition solutions_safety_wit_14 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (((Znth (i * 2 ) lv 0) % ( 2 ) ) = 1) |] 
  &&  [| ((i * 2 ) < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto (i) (lv))) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> (s + (Znth (i * 2 ) lv 0) ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition solutions_entail_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) ,
  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| ((2 * 0 ) <= (lst_size_pre + 1 )) |] 
  &&  [| (0 = (sum_odd_at_even_upto (0) (lv))) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition solutions_entail_wit_2_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (((Znth (i * 2 ) lv 0) % ( 2 ) ) = 1) |] 
  &&  [| ((i * 2 ) < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto (i) (lv))) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((2 * (i + 1 ) ) <= (lst_size_pre + 1 )) |] 
  &&  [| ((s + (Znth (i * 2 ) lv 0) ) = (sum_odd_at_even_upto ((i + 1 )) (lv))) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition solutions_entail_wit_2_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (((Znth (i * 2 ) lv 0) % ( 2 ) ) <> 1) |] 
  &&  [| ((i * 2 ) < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto (i) (lv))) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((2 * (i + 1 ) ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto ((i + 1 )) (lv))) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition solutions_return_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((i * 2 ) >= lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto (i) (lv))) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (problem_121_spec_z lv s ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition solutions_partial_solve_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((i * 2 ) < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto (i) (lv))) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| ((i * 2 ) < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto (i) (lv))) |]
  &&  (((lst_pre + ((i * 2 ) * sizeof(INT) ) )) # Int  |-> (Znth (i * 2 ) lv 0))
  **  (IntArray.missing_i lst_pre (i * 2 ) 0 lst_size_pre lv )
.

Definition solutions_partial_solve_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (((Znth (i * 2 ) lv 0) % ( 2 ) ) = 1) |] 
  &&  [| ((i * 2 ) < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto (i) (lv))) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (((Znth (i * 2 ) lv 0) % ( 2 ) ) = 1) |] 
  &&  [| ((i * 2 ) < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_121_pre_z lv ) |] 
  &&  [| (sum_odd_at_even_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= (lst_size_pre + 1 )) |] 
  &&  [| (s = (sum_odd_at_even_upto (i) (lv))) |]
  &&  (((lst_pre + ((i * 2 ) * sizeof(INT) ) )) # Int  |-> (Znth (i * 2 ) lv 0))
  **  (IntArray.missing_i lst_pre (i * 2 ) 0 lst_size_pre lv )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_solutions_safety_wit_1 : solutions_safety_wit_1.
Axiom proof_of_solutions_safety_wit_2 : solutions_safety_wit_2.
Axiom proof_of_solutions_safety_wit_3 : solutions_safety_wit_3.
Axiom proof_of_solutions_safety_wit_4 : solutions_safety_wit_4.
Axiom proof_of_solutions_safety_wit_5 : solutions_safety_wit_5.
Axiom proof_of_solutions_safety_wit_6 : solutions_safety_wit_6.
Axiom proof_of_solutions_safety_wit_7 : solutions_safety_wit_7.
Axiom proof_of_solutions_safety_wit_8 : solutions_safety_wit_8.
Axiom proof_of_solutions_safety_wit_9 : solutions_safety_wit_9.
Axiom proof_of_solutions_safety_wit_10 : solutions_safety_wit_10.
Axiom proof_of_solutions_safety_wit_11 : solutions_safety_wit_11.
Axiom proof_of_solutions_safety_wit_12 : solutions_safety_wit_12.
Axiom proof_of_solutions_safety_wit_13 : solutions_safety_wit_13.
Axiom proof_of_solutions_safety_wit_14 : solutions_safety_wit_14.
Axiom proof_of_solutions_entail_wit_1 : solutions_entail_wit_1.
Axiom proof_of_solutions_entail_wit_2_1 : solutions_entail_wit_2_1.
Axiom proof_of_solutions_entail_wit_2_2 : solutions_entail_wit_2_2.
Axiom proof_of_solutions_return_wit_1 : solutions_return_wit_1.
Axiom proof_of_solutions_partial_solve_wit_1 : solutions_partial_solve_wit_1.
Axiom proof_of_solutions_partial_solve_wit_2 : solutions_partial_solve_wit_2.

End VC_Correct.

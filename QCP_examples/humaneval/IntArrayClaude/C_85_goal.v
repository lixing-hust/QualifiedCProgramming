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
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import int_array_strategy_goal.
From SimpleC.EE Require Import int_array_strategy_proof.
From SimpleC.EE Require Import uint_array_strategy_goal.
From SimpleC.EE Require Import uint_array_strategy_proof.
From SimpleC.EE Require Import undef_uint_array_strategy_goal.
From SimpleC.EE Require Import undef_uint_array_strategy_proof.
From SimpleC.EE Require Import array_shape_strategy_goal.
From SimpleC.EE Require Import array_shape_strategy_proof.

(*----- Function add -----*)

Definition add_safety_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) ,
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition add_safety_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) ,
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Int  |-> 0)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition add_safety_wit_3 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst)
  **  (IntArray.full lst lst_size_pre lv )
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
|--
  [| (((i * 2 ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((i * 2 ) + 1 )) |]
.

Definition add_safety_wit_4 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst)
  **  (IntArray.full lst lst_size_pre lv )
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
|--
  [| ((i * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i * 2 )) |]
.

Definition add_safety_wit_5 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst)
  **  (IntArray.full lst lst_size_pre lv )
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition add_safety_wit_6 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst)
  **  (IntArray.full lst lst_size_pre lv )
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition add_safety_wit_7 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (IntArray.full lst lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
|--
  [| (((Znth ((i * 2 ) + 1 ) lv 0) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition add_safety_wit_8 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst)
  **  (IntArray.full lst lst_size_pre lv )
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
|--
  [| (((i * 2 ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((i * 2 ) + 1 )) |]
.

Definition add_safety_wit_9 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst)
  **  (IntArray.full lst lst_size_pre lv )
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
|--
  [| ((i * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i * 2 )) |]
.

Definition add_safety_wit_10 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst)
  **  (IntArray.full lst lst_size_pre lv )
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition add_safety_wit_11 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst)
  **  (IntArray.full lst lst_size_pre lv )
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition add_safety_wit_12 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (IntArray.full lst lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition add_safety_wit_13 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (IntArray.full lst lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition add_safety_wit_14 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) = 0) |] 
  &&  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (IntArray.full lst lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
|--
  [| ((s + (Znth ((i * 2 ) + 1 ) lv 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (s + (Znth ((i * 2 ) + 1 ) lv 0) )) |]
.

Definition add_safety_wit_15 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) = 0) |] 
  &&  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (IntArray.full lst lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
|--
  [| (((i * 2 ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((i * 2 ) + 1 )) |]
.

Definition add_safety_wit_16 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) = 0) |] 
  &&  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (IntArray.full lst lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
|--
  [| ((i * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i * 2 )) |]
.

Definition add_safety_wit_17 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) = 0) |] 
  &&  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (IntArray.full lst lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition add_safety_wit_18 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) = 0) |] 
  &&  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (IntArray.full lst lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition add_safety_wit_19 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) = 0) |] 
  &&  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (IntArray.full lst lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> (s + (Znth ((i * 2 ) + 1 ) lv 0) ))
  **  ((( &( "lst" ) )) # Ptr  |-> lst)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition add_safety_wit_20 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) <> 0) |] 
  &&  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (IntArray.full lst lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition add_entail_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) ,
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (0 <= 0) |] 
  &&  [| ((2 * 0 ) <= lst_size_pre) |] 
  &&  [| (0 = (sum_even_at_odd_upto (0) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition add_entail_wit_2_1 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) <> 0) |] 
  &&  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (IntArray.full lst lst_size_pre lv )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((2 * (i + 1 ) ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto ((i + 1 )) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (IntArray.full lst lst_size_pre lv )
.

Definition add_entail_wit_2_2 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) = 0) |] 
  &&  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (IntArray.full lst lst_size_pre lv )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((2 * (i + 1 ) ) <= lst_size_pre) |] 
  &&  [| ((s + (Znth ((i * 2 ) + 1 ) lv 0) ) = (sum_even_at_odd_upto ((i + 1 )) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (IntArray.full lst lst_size_pre lv )
.

Definition add_return_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (((i * 2 ) + 1 ) >= lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (IntArray.full lst lst_size_pre lv )
|--
  [| (s = (sum_even_at_odd (lv))) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition add_partial_solve_wit_1 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (IntArray.full lst lst_size_pre lv )
|--
  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (((lst + (((i * 2 ) + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth ((i * 2 ) + 1 ) lv 0))
  **  (IntArray.missing_i lst ((i * 2 ) + 1 ) 0 lst_size_pre lv )
.

Definition add_partial_solve_wit_2 := 
forall (lst_size_pre: Z) (lv: (@list Z)) (lst: Z) (s: Z) (i: Z) ,
  [| (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) = 0) |] 
  &&  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (IntArray.full lst lst_size_pre lv )
|--
  [| (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) = 0) |] 
  &&  [| (((i * 2 ) + 1 ) < lst_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((2 * i ) <= lst_size_pre) |] 
  &&  [| (s = (sum_even_at_odd_upto (i) (lv))) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |]
  &&  (((lst + (((i * 2 ) + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth ((i * 2 ) + 1 ) lv 0))
  **  (IntArray.missing_i lst ((i * 2 ) + 1 ) 0 lst_size_pre lv )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_add_safety_wit_1 : add_safety_wit_1.
Axiom proof_of_add_safety_wit_2 : add_safety_wit_2.
Axiom proof_of_add_safety_wit_3 : add_safety_wit_3.
Axiom proof_of_add_safety_wit_4 : add_safety_wit_4.
Axiom proof_of_add_safety_wit_5 : add_safety_wit_5.
Axiom proof_of_add_safety_wit_6 : add_safety_wit_6.
Axiom proof_of_add_safety_wit_7 : add_safety_wit_7.
Axiom proof_of_add_safety_wit_8 : add_safety_wit_8.
Axiom proof_of_add_safety_wit_9 : add_safety_wit_9.
Axiom proof_of_add_safety_wit_10 : add_safety_wit_10.
Axiom proof_of_add_safety_wit_11 : add_safety_wit_11.
Axiom proof_of_add_safety_wit_12 : add_safety_wit_12.
Axiom proof_of_add_safety_wit_13 : add_safety_wit_13.
Axiom proof_of_add_safety_wit_14 : add_safety_wit_14.
Axiom proof_of_add_safety_wit_15 : add_safety_wit_15.
Axiom proof_of_add_safety_wit_16 : add_safety_wit_16.
Axiom proof_of_add_safety_wit_17 : add_safety_wit_17.
Axiom proof_of_add_safety_wit_18 : add_safety_wit_18.
Axiom proof_of_add_safety_wit_19 : add_safety_wit_19.
Axiom proof_of_add_safety_wit_20 : add_safety_wit_20.
Axiom proof_of_add_entail_wit_1 : add_entail_wit_1.
Axiom proof_of_add_entail_wit_2_1 : add_entail_wit_2_1.
Axiom proof_of_add_entail_wit_2_2 : add_entail_wit_2_2.
Axiom proof_of_add_return_wit_1 : add_return_wit_1.
Axiom proof_of_add_partial_solve_wit_1 : add_partial_solve_wit_1.
Axiom proof_of_add_partial_solve_wit_2 : add_partial_solve_wit_2.

End VC_Correct.

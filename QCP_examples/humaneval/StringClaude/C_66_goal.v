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
Require Import coins_66.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function digitSum -----*)

Definition digitSum_safety_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |]
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition digitSum_safety_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition digitSum_safety_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (sum_upper_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  [| (65 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 65) |]
.

Definition digitSum_safety_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (sum_upper_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  [| (90 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 90) |]
.

Definition digitSum_safety_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (sum_upper_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  [| ((sum + (Znth i (app (l) ((cons (0) (nil)))) 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (sum + (Znth i (app (l) ((cons (0) (nil)))) 0) )) |]
.

Definition digitSum_safety_wit_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (sum_upper_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition digitSum_safety_wit_7 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (sum_upper_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition digitSum_safety_wit_8 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (sum_upper_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (Znth i (app (l) ((cons (0) (nil)))) 0) ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition digitSum_entail_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (0 = (sum_upper_upto (0) (l))) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition digitSum_entail_wit_2_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (sum_upper_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((sum + (Znth i (app (l) ((cons (0) (nil)))) 0) ) = (sum_upper_upto ((i + 1 )) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition digitSum_entail_wit_2_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (sum_upper_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (sum = (sum_upper_upto ((i + 1 )) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition digitSum_entail_wit_2_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (sum_upper_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (sum = (sum_upper_upto ((i + 1 )) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition digitSum_return_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (sum_upper_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_66_spec_z l sum ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition digitSum_partial_solve_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition digitSum_partial_solve_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (sum_upper_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (sum_upper_upto (i) (l))) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition digitSum_partial_solve_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (sum_upper_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (sum_upper_upto (i) (l))) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition digitSum_partial_solve_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (sum_upper_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_66_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (digit_sum_int_range l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (sum_upper_upto (i) (l))) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_digitSum_safety_wit_1 : digitSum_safety_wit_1.
Axiom proof_of_digitSum_safety_wit_2 : digitSum_safety_wit_2.
Axiom proof_of_digitSum_safety_wit_3 : digitSum_safety_wit_3.
Axiom proof_of_digitSum_safety_wit_4 : digitSum_safety_wit_4.
Axiom proof_of_digitSum_safety_wit_5 : digitSum_safety_wit_5.
Axiom proof_of_digitSum_safety_wit_6 : digitSum_safety_wit_6.
Axiom proof_of_digitSum_safety_wit_7 : digitSum_safety_wit_7.
Axiom proof_of_digitSum_safety_wit_8 : digitSum_safety_wit_8.
Axiom proof_of_digitSum_entail_wit_1 : digitSum_entail_wit_1.
Axiom proof_of_digitSum_entail_wit_2_1 : digitSum_entail_wit_2_1.
Axiom proof_of_digitSum_entail_wit_2_2 : digitSum_entail_wit_2_2.
Axiom proof_of_digitSum_entail_wit_2_3 : digitSum_entail_wit_2_3.
Axiom proof_of_digitSum_return_wit_1 : digitSum_return_wit_1.
Axiom proof_of_digitSum_partial_solve_wit_1 : digitSum_partial_solve_wit_1.
Axiom proof_of_digitSum_partial_solve_wit_2 : digitSum_partial_solve_wit_2.
Axiom proof_of_digitSum_partial_solve_wit_3 : digitSum_partial_solve_wit_3.
Axiom proof_of_digitSum_partial_solve_wit_4 : digitSum_partial_solve_wit_4.

End VC_Correct.

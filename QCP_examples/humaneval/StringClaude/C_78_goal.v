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
Require Import coins_78.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function hex_key -----*)

Definition hex_key_safety_wit_1 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hex_key_safety_wit_2 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "out" ) )) # Int  |-> 0)
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hex_key_safety_wit_3 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| (50 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 50) |]
.

Definition hex_key_safety_wit_4 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| (51 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 51) |]
.

Definition hex_key_safety_wit_5 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| (53 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 53) |]
.

Definition hex_key_safety_wit_6 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| (55 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 55) |]
.

Definition hex_key_safety_wit_7 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| (66 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 66) |]
.

Definition hex_key_safety_wit_8 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 66) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| (68 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 68) |]
.

Definition hex_key_safety_wit_9 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 68) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 66) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| ((out + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (out + 1 )) |]
.

Definition hex_key_safety_wit_10 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 68) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 66) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hex_key_safety_wit_11 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| ((out + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (out + 1 )) |]
.

Definition hex_key_safety_wit_12 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hex_key_safety_wit_13 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| ((out + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (out + 1 )) |]
.

Definition hex_key_safety_wit_14 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hex_key_safety_wit_15 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| ((out + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (out + 1 )) |]
.

Definition hex_key_safety_wit_16 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hex_key_safety_wit_17 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| ((out + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (out + 1 )) |]
.

Definition hex_key_safety_wit_18 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hex_key_safety_wit_19 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 66) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| ((out + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (out + 1 )) |]
.

Definition hex_key_safety_wit_20 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 66) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition hex_key_safety_wit_21 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 68) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 66) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition hex_key_safety_wit_22 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 66) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> (out + 1 ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition hex_key_safety_wit_23 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> (out + 1 ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition hex_key_safety_wit_24 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> (out + 1 ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition hex_key_safety_wit_25 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> (out + 1 ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition hex_key_safety_wit_26 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> (out + 1 ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition hex_key_safety_wit_27 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 68) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 66) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> (out + 1 ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition hex_key_entail_wit_1 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 = (count_prime_hex_upto (0) (l))) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition hex_key_entail_wit_2_1 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 68) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 66) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= (out + 1 )) |] 
  &&  [| ((out + 1 ) <= (i + 1 )) |] 
  &&  [| ((out + 1 ) = (count_prime_hex_upto ((i + 1 )) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition hex_key_entail_wit_2_2 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= (out + 1 )) |] 
  &&  [| ((out + 1 ) <= (i + 1 )) |] 
  &&  [| ((out + 1 ) = (count_prime_hex_upto ((i + 1 )) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition hex_key_entail_wit_2_3 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= (out + 1 )) |] 
  &&  [| ((out + 1 ) <= (i + 1 )) |] 
  &&  [| ((out + 1 ) = (count_prime_hex_upto ((i + 1 )) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition hex_key_entail_wit_2_4 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= (out + 1 )) |] 
  &&  [| ((out + 1 ) <= (i + 1 )) |] 
  &&  [| ((out + 1 ) = (count_prime_hex_upto ((i + 1 )) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition hex_key_entail_wit_2_5 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= (out + 1 )) |] 
  &&  [| ((out + 1 ) <= (i + 1 )) |] 
  &&  [| ((out + 1 ) = (count_prime_hex_upto ((i + 1 )) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition hex_key_entail_wit_2_6 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 66) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= (out + 1 )) |] 
  &&  [| ((out + 1 ) <= (i + 1 )) |] 
  &&  [| ((out + 1 ) = (count_prime_hex_upto ((i + 1 )) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition hex_key_entail_wit_2_7 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 68) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 66) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= (i + 1 )) |] 
  &&  [| (out = (count_prime_hex_upto ((i + 1 )) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition hex_key_return_wit_1 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_78_spec_z l out ) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition hex_key_partial_solve_wit_1 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition hex_key_partial_solve_wit_2 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (((num_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i num_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition hex_key_partial_solve_wit_3 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (((num_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i num_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition hex_key_partial_solve_wit_4 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (((num_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i num_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition hex_key_partial_solve_wit_5 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (((num_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i num_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition hex_key_partial_solve_wit_6 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (((num_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i num_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition hex_key_partial_solve_wit_7 := 
forall (num_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 66) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (CharArray.full num_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 66) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 55) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 53) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 51) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 50) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_78_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= out) |] 
  &&  [| (out <= i) |] 
  &&  [| (out = (count_prime_hex_upto (i) (l))) |]
  &&  (((num_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i num_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_hex_key_safety_wit_1 : hex_key_safety_wit_1.
Axiom proof_of_hex_key_safety_wit_2 : hex_key_safety_wit_2.
Axiom proof_of_hex_key_safety_wit_3 : hex_key_safety_wit_3.
Axiom proof_of_hex_key_safety_wit_4 : hex_key_safety_wit_4.
Axiom proof_of_hex_key_safety_wit_5 : hex_key_safety_wit_5.
Axiom proof_of_hex_key_safety_wit_6 : hex_key_safety_wit_6.
Axiom proof_of_hex_key_safety_wit_7 : hex_key_safety_wit_7.
Axiom proof_of_hex_key_safety_wit_8 : hex_key_safety_wit_8.
Axiom proof_of_hex_key_safety_wit_9 : hex_key_safety_wit_9.
Axiom proof_of_hex_key_safety_wit_10 : hex_key_safety_wit_10.
Axiom proof_of_hex_key_safety_wit_11 : hex_key_safety_wit_11.
Axiom proof_of_hex_key_safety_wit_12 : hex_key_safety_wit_12.
Axiom proof_of_hex_key_safety_wit_13 : hex_key_safety_wit_13.
Axiom proof_of_hex_key_safety_wit_14 : hex_key_safety_wit_14.
Axiom proof_of_hex_key_safety_wit_15 : hex_key_safety_wit_15.
Axiom proof_of_hex_key_safety_wit_16 : hex_key_safety_wit_16.
Axiom proof_of_hex_key_safety_wit_17 : hex_key_safety_wit_17.
Axiom proof_of_hex_key_safety_wit_18 : hex_key_safety_wit_18.
Axiom proof_of_hex_key_safety_wit_19 : hex_key_safety_wit_19.
Axiom proof_of_hex_key_safety_wit_20 : hex_key_safety_wit_20.
Axiom proof_of_hex_key_safety_wit_21 : hex_key_safety_wit_21.
Axiom proof_of_hex_key_safety_wit_22 : hex_key_safety_wit_22.
Axiom proof_of_hex_key_safety_wit_23 : hex_key_safety_wit_23.
Axiom proof_of_hex_key_safety_wit_24 : hex_key_safety_wit_24.
Axiom proof_of_hex_key_safety_wit_25 : hex_key_safety_wit_25.
Axiom proof_of_hex_key_safety_wit_26 : hex_key_safety_wit_26.
Axiom proof_of_hex_key_safety_wit_27 : hex_key_safety_wit_27.
Axiom proof_of_hex_key_entail_wit_1 : hex_key_entail_wit_1.
Axiom proof_of_hex_key_entail_wit_2_1 : hex_key_entail_wit_2_1.
Axiom proof_of_hex_key_entail_wit_2_2 : hex_key_entail_wit_2_2.
Axiom proof_of_hex_key_entail_wit_2_3 : hex_key_entail_wit_2_3.
Axiom proof_of_hex_key_entail_wit_2_4 : hex_key_entail_wit_2_4.
Axiom proof_of_hex_key_entail_wit_2_5 : hex_key_entail_wit_2_5.
Axiom proof_of_hex_key_entail_wit_2_6 : hex_key_entail_wit_2_6.
Axiom proof_of_hex_key_entail_wit_2_7 : hex_key_entail_wit_2_7.
Axiom proof_of_hex_key_return_wit_1 : hex_key_return_wit_1.
Axiom proof_of_hex_key_partial_solve_wit_1 : hex_key_partial_solve_wit_1.
Axiom proof_of_hex_key_partial_solve_wit_2 : hex_key_partial_solve_wit_2.
Axiom proof_of_hex_key_partial_solve_wit_3 : hex_key_partial_solve_wit_3.
Axiom proof_of_hex_key_partial_solve_wit_4 : hex_key_partial_solve_wit_4.
Axiom proof_of_hex_key_partial_solve_wit_5 : hex_key_partial_solve_wit_5.
Axiom proof_of_hex_key_partial_solve_wit_6 : hex_key_partial_solve_wit_6.
Axiom proof_of_hex_key_partial_solve_wit_7 : hex_key_partial_solve_wit_7.

End VC_Correct.

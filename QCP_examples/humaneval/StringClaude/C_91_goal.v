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
Require Import coins_91.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function is_bored -----*)

Definition is_bored_safety_wit_1 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |]
  &&  ((( &( "isstart" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_bored_safety_wit_2 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |]
  &&  ((( &( "isi" ) )) # Int  |->_)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_bored_safety_wit_3 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |]
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_bored_safety_wit_4 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_bored_safety_wit_5 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition is_bored_safety_wit_6 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_bored_safety_wit_7 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| (isi = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_bored_safety_wit_8 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| (isi = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| ((sum + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (sum + 1 )) |]
.

Definition is_bored_safety_wit_9 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| (isi = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_bored_safety_wit_10 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| (isi <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  [| (73 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 73) |]
.

Definition is_bored_safety_wit_11 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  [| (73 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 73) |]
.

Definition is_bored_safety_wit_12 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| (isi = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (73 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 73) |]
.

Definition is_bored_safety_wit_13 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| (isi <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  [| False |]
.

Definition is_bored_safety_wit_14 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| (isi = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| False |]
.

Definition is_bored_safety_wit_15 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_bored_safety_wit_16 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| (isstart = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_bored_safety_wit_17 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| (isstart <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_bored_safety_wit_18 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_bored_safety_wit_19 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_bored_safety_wit_20 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_bored_safety_wit_21 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition is_bored_safety_wit_22 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition is_bored_safety_wit_23 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition is_bored_safety_wit_24 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| (isstart <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition is_bored_safety_wit_25 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| (isstart = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition is_bored_safety_wit_26 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| False |]
.

Definition is_bored_safety_wit_27 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| False |]
.

Definition is_bored_safety_wit_28 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| False |]
.

Definition is_bored_safety_wit_29 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (isstart <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| False |]
.

Definition is_bored_safety_wit_30 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (isstart = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  [| False |]
.

Definition is_bored_safety_wit_31 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (isstart = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_bored_safety_wit_32 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (isstart <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_bored_safety_wit_33 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_bored_safety_wit_34 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (46 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 46) |]
.

Definition is_bored_safety_wit_35 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (46 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 46) |]
.

Definition is_bored_safety_wit_36 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (46 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 46) |]
.

Definition is_bored_safety_wit_37 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (isstart <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (46 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 46) |]
.

Definition is_bored_safety_wit_38 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (isstart = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  [| (46 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 46) |]
.

Definition is_bored_safety_wit_39 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| False |]
.

Definition is_bored_safety_wit_40 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| False |]
.

Definition is_bored_safety_wit_41 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (isstart <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| False |]
.

Definition is_bored_safety_wit_42 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (isstart = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  [| False |]
.

Definition is_bored_safety_wit_43 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (isstart = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  [| (63 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 63) |]
.

Definition is_bored_safety_wit_44 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (isstart <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (63 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 63) |]
.

Definition is_bored_safety_wit_45 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (63 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 63) |]
.

Definition is_bored_safety_wit_46 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (63 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 63) |]
.

Definition is_bored_safety_wit_47 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (63 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 63) |]
.

Definition is_bored_safety_wit_48 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (isstart = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  [| False |]
.

Definition is_bored_safety_wit_49 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (isstart <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| False |]
.

Definition is_bored_safety_wit_50 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| False |]
.

Definition is_bored_safety_wit_51 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| False |]
.

Definition is_bored_safety_wit_52 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (isstart = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  [| (33 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 33) |]
.

Definition is_bored_safety_wit_53 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (isstart <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (33 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 33) |]
.

Definition is_bored_safety_wit_54 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (33 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 33) |]
.

Definition is_bored_safety_wit_55 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (33 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 33) |]
.

Definition is_bored_safety_wit_56 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (33 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 33) |]
.

Definition is_bored_safety_wit_57 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 33) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (isstart = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  [| False |]
.

Definition is_bored_safety_wit_58 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 33) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (isstart <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| False |]
.

Definition is_bored_safety_wit_59 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 33) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| False |]
.

Definition is_bored_safety_wit_60 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 33) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| False |]
.

Definition is_bored_safety_wit_61 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 33) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_bored_safety_wit_62 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_bored_safety_wit_63 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_bored_safety_wit_64 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (isstart = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_bored_safety_wit_65 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (isstart <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_bored_safety_wit_66 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_bored_safety_wit_67 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_bored_safety_wit_68 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_bored_safety_wit_69 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_bored_safety_wit_70 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_bored_safety_wit_71 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 33) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_bored_entail_wit_1 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (0 = (bored_sum_prefix_z (0) (l))) |] 
  &&  [| (1 = (bored_isstart_prefix_z (0) (l))) |] 
  &&  [| (0 = (bored_isi_prefix_z (0) (l))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_bored_entail_wit_2_1 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 33) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (1 = (bored_isstart_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (bored_isi_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= (i + 1 )) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_bored_entail_wit_2_2 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (1 = (bored_isstart_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (bored_isi_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= (i + 1 )) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_bored_entail_wit_2_3 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (1 = (bored_isstart_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (bored_isi_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= (i + 1 )) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_bored_entail_wit_2_4 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (bored_isi_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= (i + 1 )) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_bored_entail_wit_2_5 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| (isi = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((sum + 1 ) = (bored_sum_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (bored_isi_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= (sum + 1 )) |] 
  &&  [| ((sum + 1 ) <= (i + 1 )) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_bored_entail_wit_2_6 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (bored_isstart_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (bored_isi_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= (i + 1 )) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_bored_entail_wit_2_7 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (isstart <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (bored_isstart_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (bored_isi_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= (i + 1 )) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_bored_entail_wit_2_8 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (isstart = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (bored_isstart_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (1 = (bored_isi_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= (i + 1 )) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_bored_return_wit_1 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_91_spec_z l sum ) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_bored_partial_solve_wit_1 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_bored_partial_solve_wit_2 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_91_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (sum = (bored_sum_prefix_z (i) (l))) |] 
  &&  [| (isstart = (bored_isstart_prefix_z (i) (l))) |] 
  &&  [| (isi = (bored_isi_prefix_z (i) (l))) |] 
  &&  [| (0 <= sum) |] 
  &&  [| (sum <= i) |]
  &&  (((S_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i S_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_is_bored_safety_wit_1 : is_bored_safety_wit_1.
Axiom proof_of_is_bored_safety_wit_2 : is_bored_safety_wit_2.
Axiom proof_of_is_bored_safety_wit_3 : is_bored_safety_wit_3.
Axiom proof_of_is_bored_safety_wit_4 : is_bored_safety_wit_4.
Axiom proof_of_is_bored_safety_wit_5 : is_bored_safety_wit_5.
Axiom proof_of_is_bored_safety_wit_6 : is_bored_safety_wit_6.
Axiom proof_of_is_bored_safety_wit_7 : is_bored_safety_wit_7.
Axiom proof_of_is_bored_safety_wit_8 : is_bored_safety_wit_8.
Axiom proof_of_is_bored_safety_wit_9 : is_bored_safety_wit_9.
Axiom proof_of_is_bored_safety_wit_10 : is_bored_safety_wit_10.
Axiom proof_of_is_bored_safety_wit_11 : is_bored_safety_wit_11.
Axiom proof_of_is_bored_safety_wit_12 : is_bored_safety_wit_12.
Axiom proof_of_is_bored_safety_wit_13 : is_bored_safety_wit_13.
Axiom proof_of_is_bored_safety_wit_14 : is_bored_safety_wit_14.
Axiom proof_of_is_bored_safety_wit_15 : is_bored_safety_wit_15.
Axiom proof_of_is_bored_safety_wit_16 : is_bored_safety_wit_16.
Axiom proof_of_is_bored_safety_wit_17 : is_bored_safety_wit_17.
Axiom proof_of_is_bored_safety_wit_18 : is_bored_safety_wit_18.
Axiom proof_of_is_bored_safety_wit_19 : is_bored_safety_wit_19.
Axiom proof_of_is_bored_safety_wit_20 : is_bored_safety_wit_20.
Axiom proof_of_is_bored_safety_wit_21 : is_bored_safety_wit_21.
Axiom proof_of_is_bored_safety_wit_22 : is_bored_safety_wit_22.
Axiom proof_of_is_bored_safety_wit_23 : is_bored_safety_wit_23.
Axiom proof_of_is_bored_safety_wit_24 : is_bored_safety_wit_24.
Axiom proof_of_is_bored_safety_wit_25 : is_bored_safety_wit_25.
Axiom proof_of_is_bored_safety_wit_26 : is_bored_safety_wit_26.
Axiom proof_of_is_bored_safety_wit_27 : is_bored_safety_wit_27.
Axiom proof_of_is_bored_safety_wit_28 : is_bored_safety_wit_28.
Axiom proof_of_is_bored_safety_wit_29 : is_bored_safety_wit_29.
Axiom proof_of_is_bored_safety_wit_30 : is_bored_safety_wit_30.
Axiom proof_of_is_bored_safety_wit_31 : is_bored_safety_wit_31.
Axiom proof_of_is_bored_safety_wit_32 : is_bored_safety_wit_32.
Axiom proof_of_is_bored_safety_wit_33 : is_bored_safety_wit_33.
Axiom proof_of_is_bored_safety_wit_34 : is_bored_safety_wit_34.
Axiom proof_of_is_bored_safety_wit_35 : is_bored_safety_wit_35.
Axiom proof_of_is_bored_safety_wit_36 : is_bored_safety_wit_36.
Axiom proof_of_is_bored_safety_wit_37 : is_bored_safety_wit_37.
Axiom proof_of_is_bored_safety_wit_38 : is_bored_safety_wit_38.
Axiom proof_of_is_bored_safety_wit_39 : is_bored_safety_wit_39.
Axiom proof_of_is_bored_safety_wit_40 : is_bored_safety_wit_40.
Axiom proof_of_is_bored_safety_wit_41 : is_bored_safety_wit_41.
Axiom proof_of_is_bored_safety_wit_42 : is_bored_safety_wit_42.
Axiom proof_of_is_bored_safety_wit_43 : is_bored_safety_wit_43.
Axiom proof_of_is_bored_safety_wit_44 : is_bored_safety_wit_44.
Axiom proof_of_is_bored_safety_wit_45 : is_bored_safety_wit_45.
Axiom proof_of_is_bored_safety_wit_46 : is_bored_safety_wit_46.
Axiom proof_of_is_bored_safety_wit_47 : is_bored_safety_wit_47.
Axiom proof_of_is_bored_safety_wit_48 : is_bored_safety_wit_48.
Axiom proof_of_is_bored_safety_wit_49 : is_bored_safety_wit_49.
Axiom proof_of_is_bored_safety_wit_50 : is_bored_safety_wit_50.
Axiom proof_of_is_bored_safety_wit_51 : is_bored_safety_wit_51.
Axiom proof_of_is_bored_safety_wit_52 : is_bored_safety_wit_52.
Axiom proof_of_is_bored_safety_wit_53 : is_bored_safety_wit_53.
Axiom proof_of_is_bored_safety_wit_54 : is_bored_safety_wit_54.
Axiom proof_of_is_bored_safety_wit_55 : is_bored_safety_wit_55.
Axiom proof_of_is_bored_safety_wit_56 : is_bored_safety_wit_56.
Axiom proof_of_is_bored_safety_wit_57 : is_bored_safety_wit_57.
Axiom proof_of_is_bored_safety_wit_58 : is_bored_safety_wit_58.
Axiom proof_of_is_bored_safety_wit_59 : is_bored_safety_wit_59.
Axiom proof_of_is_bored_safety_wit_60 : is_bored_safety_wit_60.
Axiom proof_of_is_bored_safety_wit_61 : is_bored_safety_wit_61.
Axiom proof_of_is_bored_safety_wit_62 : is_bored_safety_wit_62.
Axiom proof_of_is_bored_safety_wit_63 : is_bored_safety_wit_63.
Axiom proof_of_is_bored_safety_wit_64 : is_bored_safety_wit_64.
Axiom proof_of_is_bored_safety_wit_65 : is_bored_safety_wit_65.
Axiom proof_of_is_bored_safety_wit_66 : is_bored_safety_wit_66.
Axiom proof_of_is_bored_safety_wit_67 : is_bored_safety_wit_67.
Axiom proof_of_is_bored_safety_wit_68 : is_bored_safety_wit_68.
Axiom proof_of_is_bored_safety_wit_69 : is_bored_safety_wit_69.
Axiom proof_of_is_bored_safety_wit_70 : is_bored_safety_wit_70.
Axiom proof_of_is_bored_safety_wit_71 : is_bored_safety_wit_71.
Axiom proof_of_is_bored_entail_wit_1 : is_bored_entail_wit_1.
Axiom proof_of_is_bored_entail_wit_2_1 : is_bored_entail_wit_2_1.
Axiom proof_of_is_bored_entail_wit_2_2 : is_bored_entail_wit_2_2.
Axiom proof_of_is_bored_entail_wit_2_3 : is_bored_entail_wit_2_3.
Axiom proof_of_is_bored_entail_wit_2_4 : is_bored_entail_wit_2_4.
Axiom proof_of_is_bored_entail_wit_2_5 : is_bored_entail_wit_2_5.
Axiom proof_of_is_bored_entail_wit_2_6 : is_bored_entail_wit_2_6.
Axiom proof_of_is_bored_entail_wit_2_7 : is_bored_entail_wit_2_7.
Axiom proof_of_is_bored_entail_wit_2_8 : is_bored_entail_wit_2_8.
Axiom proof_of_is_bored_return_wit_1 : is_bored_return_wit_1.
Axiom proof_of_is_bored_partial_solve_wit_1 : is_bored_partial_solve_wit_1.
Axiom proof_of_is_bored_partial_solve_wit_2 : is_bored_partial_solve_wit_2.

End VC_Correct.

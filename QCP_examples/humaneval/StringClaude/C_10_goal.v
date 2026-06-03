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
Require Import coins_10.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function is_pal_suffix -----*)

Definition is_pal_suffix_safety_wit_1 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) ,
  [| (0 <= start_pre) |] 
  &&  [| (start_pre <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> start_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> start_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((n_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre - 1 )) |]
.

Definition is_pal_suffix_safety_wit_2 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) ,
  [| (0 <= start_pre) |] 
  &&  [| (start_pre <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> start_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> start_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_pal_suffix_safety_wit_3 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) ,
  [| (start_pre = n_pre) |] 
  &&  [| (0 <= start_pre) |] 
  &&  [| (start_pre <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "j" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "i" ) )) # Int  |-> start_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> start_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_pal_suffix_safety_wit_4 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth j (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (i < j) |] 
  &&  [| (0 <= start_pre) |] 
  &&  [| (start_pre < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (start_pre <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((i + j ) = ((n_pre + start_pre ) - 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "start" ) )) # Int  |-> start_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_pal_suffix_safety_wit_5 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth j (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (i < j) |] 
  &&  [| (0 <= start_pre) |] 
  &&  [| (start_pre < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (start_pre <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((i + j ) = ((n_pre + start_pre ) - 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "start" ) )) # Int  |-> start_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_pal_suffix_safety_wit_6 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth j (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (i < j) |] 
  &&  [| (0 <= start_pre) |] 
  &&  [| (start_pre < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (start_pre <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((i + j ) = ((n_pre + start_pre ) - 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "start" ) )) # Int  |-> start_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_pal_suffix_safety_wit_7 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth j (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (i < j) |] 
  &&  [| (0 <= start_pre) |] 
  &&  [| (start_pre < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (start_pre <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((i + j ) = ((n_pre + start_pre ) - 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "start" ) )) # Int  |-> start_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  [| ((j - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j - 1 )) |]
.

Definition is_pal_suffix_safety_wit_8 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth j (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (i < j) |] 
  &&  [| (0 <= start_pre) |] 
  &&  [| (start_pre < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (start_pre <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((i + j ) = ((n_pre + start_pre ) - 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "start" ) )) # Int  |-> start_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_pal_suffix_safety_wit_9 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  [| (i >= j) |] 
  &&  [| (0 <= start_pre) |] 
  &&  [| (start_pre < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (start_pre <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((i + j ) = ((n_pre + start_pre ) - 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "start" ) )) # Int  |-> start_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_pal_suffix_entail_wit_1 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) ,
  [| (start_pre <> n_pre) |] 
  &&  [| (0 <= start_pre) |] 
  &&  [| (start_pre <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= start_pre) |] 
  &&  [| (start_pre < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (start_pre <= start_pre) |] 
  &&  [| (start_pre <= n_pre) |] 
  &&  [| (0 <= (n_pre - 1 )) |] 
  &&  [| ((n_pre - 1 ) < n_pre) |] 
  &&  [| ((start_pre + (n_pre - 1 ) ) = ((n_pre + start_pre ) - 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (start_pre - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_pal_suffix_entail_wit_2 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth j (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (i < j) |] 
  &&  [| (0 <= start_pre) |] 
  &&  [| (start_pre < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (start_pre <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((i + j ) = ((n_pre + start_pre ) - 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= start_pre) |] 
  &&  [| (start_pre < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (start_pre <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= (j - 1 )) |] 
  &&  [| ((j - 1 ) < n_pre) |] 
  &&  [| (((i + 1 ) + (j - 1 ) ) = ((n_pre + start_pre ) - 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < ((i + 1 ) - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_pal_suffix_return_wit_1 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  [| (i >= j) |] 
  &&  [| (0 <= start_pre) |] 
  &&  [| (start_pre < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (start_pre <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((i + j ) = ((n_pre + start_pre ) - 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  ([| (1 = 0) |] 
  &&  [| ~((pal_suffix_z start_pre l )) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  ([| (1 = 1) |] 
  &&  [| (pal_suffix_z start_pre l ) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition is_pal_suffix_return_wit_2 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth j (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (i < j) |] 
  &&  [| (0 <= start_pre) |] 
  &&  [| (start_pre < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (start_pre <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((i + j ) = ((n_pre + start_pre ) - 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  ([| (0 = 0) |] 
  &&  [| ~((pal_suffix_z start_pre l )) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  ([| (0 = 1) |] 
  &&  [| (pal_suffix_z start_pre l ) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition is_pal_suffix_return_wit_3 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) ,
  [| (start_pre = n_pre) |] 
  &&  [| (0 <= start_pre) |] 
  &&  [| (start_pre <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  ([| (1 = 0) |] 
  &&  [| ~((pal_suffix_z start_pre l )) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  ([| (1 = 1) |] 
  &&  [| (pal_suffix_z start_pre l ) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition is_pal_suffix_partial_solve_wit_1 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  [| (i < j) |] 
  &&  [| (0 <= start_pre) |] 
  &&  [| (start_pre < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (start_pre <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((i + j ) = ((n_pre + start_pre ) - 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (i < j) |] 
  &&  [| (0 <= start_pre) |] 
  &&  [| (start_pre < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (start_pre <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((i + j ) = ((n_pre + start_pre ) - 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_pal_suffix_partial_solve_wit_2 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  [| (i < j) |] 
  &&  [| (0 <= start_pre) |] 
  &&  [| (start_pre < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (start_pre <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((i + j ) = ((n_pre + start_pre ) - 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (i < j) |] 
  &&  [| (0 <= start_pre) |] 
  &&  [| (start_pre < n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (start_pre <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < n_pre) |] 
  &&  [| ((i + j ) = ((n_pre + start_pre ) - 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) |]
  &&  (((s_pre + (j * sizeof(CHAR) ) )) # Char  |-> (Znth j (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre j 0 (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
.

(*----- Function make_palindrome -----*)

Definition make_palindrome_safety_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |-> retval)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition make_palindrome_safety_wit_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  [| (best <> len) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| False |]
.

Definition make_palindrome_safety_wit_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  [| (best = len) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best < len) |] 
  &&  [| (best < i) |] 
  &&  [| (pal_suffix_z best l ) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < best)) -> ~((pal_suffix_z t l ))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| False |]
.

Definition make_palindrome_safety_wit_4 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  [| (retval = 1) |] 
  &&  [| (pal_suffix_z i l ) |] 
  &&  [| (best = len) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition make_palindrome_safety_wit_5 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| ~((pal_suffix_z i l )) |] 
  &&  [| (best = len) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition make_palindrome_safety_wit_6 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  [| (retval <> 1) |] 
  &&  [| (retval = 1) |] 
  &&  [| (pal_suffix_z i l ) |] 
  &&  [| (best = len) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  [| False |]
.

Definition make_palindrome_safety_wit_7 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  [| (retval = 1) |] 
  &&  [| (retval = 0) |] 
  &&  [| ~((pal_suffix_z i l )) |] 
  &&  [| (best = len) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  [| False |]
.

Definition make_palindrome_safety_wit_8 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  [| (best <> len) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best < len) |] 
  &&  [| (best < i) |] 
  &&  [| (pal_suffix_z best l ) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < best)) -> ~((pal_suffix_z t l ))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition make_palindrome_safety_wit_9 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  [| (retval <> 1) |] 
  &&  [| (retval = 0) |] 
  &&  [| ~((pal_suffix_z i l )) |] 
  &&  [| (best = len) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition make_palindrome_safety_wit_10 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  [| (retval = 1) |] 
  &&  [| (retval = 1) |] 
  &&  [| (pal_suffix_z i l ) |] 
  &&  [| (best = len) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> i)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition make_palindrome_safety_wit_11 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  [| (best <> len) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| False |]
.

Definition make_palindrome_safety_wit_12 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  [| (best = len) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best < len) |] 
  &&  [| (best < i) |] 
  &&  [| (pal_suffix_z best l ) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < best)) -> ~((pal_suffix_z t l ))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| False |]
.

Definition make_palindrome_safety_wit_13 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  [| (best = len) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition make_palindrome_safety_wit_14 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  [| (best <> len) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best < len) |] 
  &&  [| (best < i) |] 
  &&  [| (pal_suffix_z best l ) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < best)) -> ~((pal_suffix_z t l ))) |]
  &&  ((( &( "out_len" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((len + best ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (len + best )) |]
.

Definition make_palindrome_safety_wit_15 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  [| (best = len) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  ((( &( "out_len" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> 0)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((len + 0 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (len + 0 )) |]
.

Definition make_palindrome_safety_wit_16 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  [| (best = len) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "out_len" ) )) # Int  |-> (len + 0 ))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> 0)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (((len + 0 ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((len + 0 ) + 1 )) |]
.

Definition make_palindrome_safety_wit_17 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  [| (best = len) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "out_len" ) )) # Int  |-> (len + 0 ))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> 0)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition make_palindrome_safety_wit_18 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  [| (best <> len) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best < len) |] 
  &&  [| (best < i) |] 
  &&  [| (pal_suffix_z best l ) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < best)) -> ~((pal_suffix_z t l ))) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "out_len" ) )) # Int  |-> (len + best ))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (((len + best ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((len + best ) + 1 )) |]
.

Definition make_palindrome_safety_wit_19 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  [| (best <> len) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best < len) |] 
  &&  [| (best < i) |] 
  &&  [| (pal_suffix_z best l ) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < best)) -> ~((pal_suffix_z t l ))) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "out_len" ) )) # Int  |-> (len + best ))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition make_palindrome_safety_wit_20 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (best <> len) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best < len) |] 
  &&  [| (best < i) |] 
  &&  [| (pal_suffix_z best l ) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < best)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.undef_full retval ((len + best ) + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "out_len" ) )) # Int  |-> (len + best ))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition make_palindrome_safety_wit_21 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (best = len) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.undef_full retval ((len + 0 ) + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "out_len" ) )) # Int  |-> (len + 0 ))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> 0)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition make_palindrome_safety_wit_22 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (i: Z) (out: Z) (out_len: Z) (best: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (i <= out_len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < i)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((Znth i (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition make_palindrome_safety_wit_23 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (i: Z) (out: Z) (out_len: Z) (best: Z) ,
  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (i <= out_len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < i)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |]
  &&  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (out_len + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition make_palindrome_safety_wit_24 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (k: Z) (out: Z) (out_len: Z) (i: Z) (best: Z) ,
  [| (k < best) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (i = len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= best) |] 
  &&  [| ((len + k ) <= out_len) |] 
  &&  [| ((Zlength (out_l)) = (len + k )) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < len)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |] 
  &&  [| forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < k)) -> ((Znth ((len + p_2 )) (out_l) (0)) = (Znth (((best - 1 ) - p_2 )) (l) (0)))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + k ) out_l )
  **  (CharArray.undef_seg out (len + k ) (out_len + 1 ) )
|--
  [| ((len + k ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (len + k )) |]
.

Definition make_palindrome_safety_wit_25 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (k: Z) (out: Z) (out_len: Z) (i: Z) (best: Z) ,
  [| (k < best) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (i = len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= best) |] 
  &&  [| ((len + k ) <= out_len) |] 
  &&  [| ((Zlength (out_l)) = (len + k )) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < len)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |] 
  &&  [| forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < k)) -> ((Znth ((len + p_2 )) (out_l) (0)) = (Znth (((best - 1 ) - p_2 )) (l) (0)))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + k ) out_l )
  **  (CharArray.undef_seg out (len + k ) (out_len + 1 ) )
|--
  [| (((best - 1 ) - k ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((best - 1 ) - k )) |]
.

Definition make_palindrome_safety_wit_26 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (k: Z) (out: Z) (out_len: Z) (i: Z) (best: Z) ,
  [| (k < best) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (i = len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= best) |] 
  &&  [| ((len + k ) <= out_len) |] 
  &&  [| ((Zlength (out_l)) = (len + k )) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < len)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |] 
  &&  [| forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < k)) -> ((Znth ((len + p_2 )) (out_l) (0)) = (Znth (((best - 1 ) - p_2 )) (l) (0)))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + k ) out_l )
  **  (CharArray.undef_seg out (len + k ) (out_len + 1 ) )
|--
  [| ((best - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (best - 1 )) |]
.

Definition make_palindrome_safety_wit_27 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (k: Z) (out: Z) (out_len: Z) (i: Z) (best: Z) ,
  [| (k < best) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (i = len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= best) |] 
  &&  [| ((len + k ) <= out_len) |] 
  &&  [| ((Zlength (out_l)) = (len + k )) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < len)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |] 
  &&  [| forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < k)) -> ((Znth ((len + p_2 )) (out_l) (0)) = (Znth (((best - 1 ) - p_2 )) (l) (0)))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + k ) out_l )
  **  (CharArray.undef_seg out (len + k ) (out_len + 1 ) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition make_palindrome_safety_wit_28 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (k: Z) (out: Z) (out_len: Z) (i: Z) (best: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (0 <= (len + k )) |] 
  &&  [| (k < best) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (i = len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= best) |] 
  &&  [| ((len + k ) <= out_len) |] 
  &&  [| ((Zlength (out_l)) = (len + k )) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < len)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |] 
  &&  [| forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < k)) -> ((Znth ((len + p_2 )) (out_l) (0)) = (Znth (((best - 1 ) - p_2 )) (l) (0)))) |]
  &&  (CharArray.full out ((len + k ) + 1 ) (app (out_l) ((cons ((Znth ((best - 1 ) - k ) (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out ((len + k ) + 1 ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  [| ((k + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + 1 )) |]
.

Definition make_palindrome_safety_wit_29 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (k: Z) (out: Z) (out_len: Z) (i: Z) (best: Z) ,
  [| (k >= best) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (i = len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= best) |] 
  &&  [| ((len + k ) <= out_len) |] 
  &&  [| ((Zlength (out_l)) = (len + k )) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < len)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |] 
  &&  [| forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < k)) -> ((Znth ((len + p_2 )) (out_l) (0)) = (Znth (((best - 1 ) - p_2 )) (l) (0)))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + k ) out_l )
  **  (CharArray.undef_seg out (len + k ) (out_len + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition make_palindrome_entail_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  ([| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= len) |] 
  &&  [| (retval < len) |] 
  &&  [| (retval < 0) |] 
  &&  [| (pal_suffix_z retval l ) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < retval)) -> ~((pal_suffix_z t l ))) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  ([| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= len) |] 
  &&  [| (retval = len) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < 0)) -> ~((pal_suffix_z t_2 l ))) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition make_palindrome_entail_wit_2_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  [| (retval = 1) |] 
  &&  [| (retval = 1) |] 
  &&  [| (pal_suffix_z i l ) |] 
  &&  [| (best = len) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < i)) -> ~((pal_suffix_z t_2 l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  ([| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (i < len) |] 
  &&  [| (i < (i + 1 )) |] 
  &&  [| (pal_suffix_z i l ) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  ([| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (i = len) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < (i + 1 ))) -> ~((pal_suffix_z t_2 l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition make_palindrome_entail_wit_2_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  [| (retval <> 1) |] 
  &&  [| (retval = 0) |] 
  &&  [| ~((pal_suffix_z i l )) |] 
  &&  [| (best = len) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < i)) -> ~((pal_suffix_z t_2 l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  ([| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best < len) |] 
  &&  [| (best < (i + 1 )) |] 
  &&  [| (pal_suffix_z best l ) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < best)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  ([| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < (i + 1 ))) -> ~((pal_suffix_z t_2 l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition make_palindrome_entail_wit_2_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  [| (best <> len) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best < len) |] 
  &&  [| (best < i) |] 
  &&  [| (pal_suffix_z best l ) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < best)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  ([| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best < len) |] 
  &&  [| (best < (i + 1 )) |] 
  &&  [| (pal_suffix_z best l ) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < best)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  ([| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t_2: Z) , (((0 <= t_2) /\ (t_2 < (i + 1 ))) -> ~((pal_suffix_z t_2 l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition make_palindrome_entail_wit_3_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (best = len) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.undef_full retval ((len + 0 ) + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z 0 l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 0 ) = (len + 0 )) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 0 )) |] 
  &&  [| ((len + 0 ) < INT_MAX) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (0 <= (len + 0 )) |] 
  &&  [| ((Zlength (out_l)) = 0) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < 0)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full retval 0 out_l )
  **  (CharArray.undef_seg retval 0 ((len + 0 ) + 1 ) )
.

Definition make_palindrome_entail_wit_3_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (best <> len) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best < len) |] 
  &&  [| (best < i) |] 
  &&  [| (pal_suffix_z best l ) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < best)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.undef_full retval ((len + best ) + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| ((len + best ) = (len + best )) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= (len + best )) |] 
  &&  [| ((len + best ) < INT_MAX) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (0 <= (len + best )) |] 
  &&  [| ((Zlength (out_l)) = 0) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < 0)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full retval 0 out_l )
  **  (CharArray.undef_seg retval 0 ((len + best ) + 1 ) )
.

Definition make_palindrome_entail_wit_4 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out_l_2: (@list Z)) (i: Z) (out: Z) (out_len: Z) (best: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (i <= out_len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < i)) -> ((Znth (p) (out_l_2) (0)) = (Znth (p) (l) (0)))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((Znth i (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((i + 1 ) <= out_len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < (i + 1 ))) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (out_len + 1 ) )
.

Definition make_palindrome_entail_wit_5 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out_l_2: (@list Z)) (i: Z) (out: Z) (out_len: Z) (best: Z) ,
  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (i <= out_len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < i)) -> ((Znth (p_3) (out_l_2) (0)) = (Znth (p_3) (l) (0)))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l_2 )
  **  (CharArray.undef_seg out i (out_len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (i = len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= best) |] 
  &&  [| ((len + 0 ) <= out_len) |] 
  &&  [| ((Zlength (out_l)) = (len + 0 )) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < len)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |] 
  &&  [| forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < 0)) -> ((Znth ((len + p_2 )) (out_l) (0)) = (Znth (((best - 1 ) - p_2 )) (l) (0)))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + 0 ) out_l )
  **  (CharArray.undef_seg out (len + 0 ) (out_len + 1 ) )
.

Definition make_palindrome_entail_wit_6 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out_l_2: (@list Z)) (k: Z) (out: Z) (out_len: Z) (i: Z) (best: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (0 <= (len + k )) |] 
  &&  [| (k < best) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (i = len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= best) |] 
  &&  [| ((len + k ) <= out_len) |] 
  &&  [| ((Zlength (out_l_2)) = (len + k )) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < len)) -> ((Znth (p) (out_l_2) (0)) = (Znth (p) (l) (0)))) |] 
  &&  [| forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < k)) -> ((Znth ((len + p_2 )) (out_l_2) (0)) = (Znth (((best - 1 ) - p_2 )) (l) (0)))) |]
  &&  (CharArray.full out ((len + k ) + 1 ) (app (out_l_2) ((cons ((Znth ((best - 1 ) - k ) (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out ((len + k ) + 1 ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (i = len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= (k + 1 )) |] 
  &&  [| ((k + 1 ) <= best) |] 
  &&  [| ((len + (k + 1 ) ) <= out_len) |] 
  &&  [| ((Zlength (out_l)) = (len + (k + 1 ) )) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < len)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |] 
  &&  [| forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < (k + 1 ))) -> ((Znth ((len + p_2 )) (out_l) (0)) = (Znth (((best - 1 ) - p_2 )) (l) (0)))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + (k + 1 ) ) out_l )
  **  (CharArray.undef_seg out (len + (k + 1 ) ) (out_len + 1 ) )
.

Definition make_palindrome_entail_wit_7 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out_l_2: (@list Z)) (k: Z) (out: Z) (out_len: Z) (i: Z) (best: Z) ,
  [| (0 <= (len + k )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (k >= best) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (i = len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= best) |] 
  &&  [| ((len + k ) <= out_len) |] 
  &&  [| ((Zlength (out_l_2)) = (len + k )) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < len)) -> ((Znth (p) (out_l_2) (0)) = (Znth (p) (l) (0)))) |] 
  &&  [| forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < k)) -> ((Znth ((len + p_2 )) (out_l_2) (0)) = (Znth (((best - 1 ) - p_2 )) (l) (0)))) |]
  &&  (CharArray.full out ((len + k ) + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (i = len) |] 
  &&  [| (k = best) |] 
  &&  [| (out_l = (make_pal_output_z (best) (l))) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (out_len = (Zlength (out_l))) |] 
  &&  [| (problem_10_spec_z l out_l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition make_palindrome_return_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out_l_2: (@list Z)) (best: Z) (i: Z) (k: Z) (out: Z) (out_len: Z) ,
  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (i = len) |] 
  &&  [| (k = best) |] 
  &&  [| (out_l_2 = (make_pal_output_z (best) (l))) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (out_len = (Zlength (out_l_2))) |] 
  &&  [| (problem_10_spec_z l out_l_2 ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (out_len + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| (problem_10_spec_z l out_l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out ((Zlength (out_l)) + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition make_palindrome_partial_solve_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition make_palindrome_partial_solve_wit_2_pure := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  [| (best = len) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  ((( &( "ok" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (len < INT_MAX) |]
.

Definition make_palindrome_partial_solve_wit_2_aux := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  [| (best = len) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| (best = len) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition make_palindrome_partial_solve_wit_2 := make_palindrome_partial_solve_wit_2_pure -> make_palindrome_partial_solve_wit_2_aux.

Definition make_palindrome_partial_solve_wit_3_pure := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  [| (best = len) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "out_len" ) )) # Int  |-> (len + 0 ))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> 0)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (((len + 0 ) + 1 ) > 0) |]
.

Definition make_palindrome_partial_solve_wit_3_aux := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  [| (best = len) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (((len + 0 ) + 1 ) > 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (best = len) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best = len) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition make_palindrome_partial_solve_wit_3 := make_palindrome_partial_solve_wit_3_pure -> make_palindrome_partial_solve_wit_3_aux.

Definition make_palindrome_partial_solve_wit_4_pure := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  [| (best <> len) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best < len) |] 
  &&  [| (best < i) |] 
  &&  [| (pal_suffix_z best l ) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < best)) -> ~((pal_suffix_z t l ))) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "out_len" ) )) # Int  |-> (len + best ))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (((len + best ) + 1 ) > 0) |]
.

Definition make_palindrome_partial_solve_wit_4_aux := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  [| (best <> len) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best < len) |] 
  &&  [| (best < i) |] 
  &&  [| (pal_suffix_z best l ) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < best)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (((len + best ) + 1 ) > 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (best <> len) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (best < len) |] 
  &&  [| (best < i) |] 
  &&  [| (pal_suffix_z best l ) |] 
  &&  [| forall (t: Z) , (((0 <= t) /\ (t < best)) -> ~((pal_suffix_z t l ))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition make_palindrome_partial_solve_wit_4 := make_palindrome_partial_solve_wit_4_pure -> make_palindrome_partial_solve_wit_4_aux.

Definition make_palindrome_partial_solve_wit_5 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (i: Z) (out: Z) (out_len: Z) (best: Z) ,
  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (i <= out_len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < i)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (out_len + 1 ) )
|--
  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (i <= out_len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < i)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |]
  &&  (((str_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i str_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (out_len + 1 ) )
.

Definition make_palindrome_partial_solve_wit_6 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (i: Z) (out: Z) (out_len: Z) (best: Z) ,
  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (i <= out_len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < i)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (out_len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (i <= out_len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < i)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition make_palindrome_partial_solve_wit_7 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (k: Z) (out: Z) (out_len: Z) (i: Z) (best: Z) ,
  [| (k < best) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (i = len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= best) |] 
  &&  [| ((len + k ) <= out_len) |] 
  &&  [| ((Zlength (out_l)) = (len + k )) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < len)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |] 
  &&  [| forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < k)) -> ((Znth ((len + p_2 )) (out_l) (0)) = (Znth (((best - 1 ) - p_2 )) (l) (0)))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + k ) out_l )
  **  (CharArray.undef_seg out (len + k ) (out_len + 1 ) )
|--
  [| (0 <= (len + k )) |] 
  &&  [| (k < best) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (i = len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= best) |] 
  &&  [| ((len + k ) <= out_len) |] 
  &&  [| ((Zlength (out_l)) = (len + k )) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < len)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |] 
  &&  [| forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < k)) -> ((Znth ((len + p_2 )) (out_l) (0)) = (Znth (((best - 1 ) - p_2 )) (l) (0)))) |]
  &&  (((str_pre + (((best - 1 ) - k ) * sizeof(CHAR) ) )) # Char  |-> (Znth ((best - 1 ) - k ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i str_pre ((best - 1 ) - k ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + k ) out_l )
  **  (CharArray.undef_seg out (len + k ) (out_len + 1 ) )
.

Definition make_palindrome_partial_solve_wit_8 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (k: Z) (out: Z) (out_len: Z) (i: Z) (best: Z) ,
  [| (0 <= (len + k )) |] 
  &&  [| (k < best) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (i = len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= best) |] 
  &&  [| ((len + k ) <= out_len) |] 
  &&  [| ((Zlength (out_l)) = (len + k )) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < len)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |] 
  &&  [| forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < k)) -> ((Znth ((len + p_2 )) (out_l) (0)) = (Znth (((best - 1 ) - p_2 )) (l) (0)))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + k ) out_l )
  **  (CharArray.undef_seg out (len + k ) (out_len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (0 <= (len + k )) |] 
  &&  [| (k < best) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (i = len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= best) |] 
  &&  [| ((len + k ) <= out_len) |] 
  &&  [| ((Zlength (out_l)) = (len + k )) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < len)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |] 
  &&  [| forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < k)) -> ((Znth ((len + p_2 )) (out_l) (0)) = (Znth (((best - 1 ) - p_2 )) (l) (0)))) |]
  &&  (((out + ((len + k ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (len + k ) (len + k ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + k ) out_l )
.

Definition make_palindrome_partial_solve_wit_9 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (k: Z) (out: Z) (out_len: Z) (i: Z) (best: Z) ,
  [| (k >= best) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (i = len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= best) |] 
  &&  [| ((len + k ) <= out_len) |] 
  &&  [| ((Zlength (out_l)) = (len + k )) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < len)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |] 
  &&  [| forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < k)) -> ((Znth ((len + p_2 )) (out_l) (0)) = (Znth (((best - 1 ) - p_2 )) (l) (0)))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + k ) out_l )
  **  (CharArray.undef_seg out (len + k ) (out_len + 1 ) )
|--
  [| (0 <= (len + k )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (k >= best) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < (INT_MAX ÷ 2 )) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_10_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (first_pal_suffix_z best l ) |] 
  &&  [| (i = len) |] 
  &&  [| (0 <= best) |] 
  &&  [| (best <= len) |] 
  &&  [| (out_len = (len + best )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len < INT_MAX) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= best) |] 
  &&  [| ((len + k ) <= out_len) |] 
  &&  [| ((Zlength (out_l)) = (len + k )) |] 
  &&  [| forall (p: Z) , (((0 <= p) /\ (p < len)) -> ((Znth (p) (out_l) (0)) = (Znth (p) (l) (0)))) |] 
  &&  [| forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < k)) -> ((Znth ((len + p_2 )) (out_l) (0)) = (Znth (((best - 1 ) - p_2 )) (l) (0)))) |]
  &&  (((out + (out_len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out out_len (len + k ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + k ) out_l )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_is_pal_suffix_safety_wit_1 : is_pal_suffix_safety_wit_1.
Axiom proof_of_is_pal_suffix_safety_wit_2 : is_pal_suffix_safety_wit_2.
Axiom proof_of_is_pal_suffix_safety_wit_3 : is_pal_suffix_safety_wit_3.
Axiom proof_of_is_pal_suffix_safety_wit_4 : is_pal_suffix_safety_wit_4.
Axiom proof_of_is_pal_suffix_safety_wit_5 : is_pal_suffix_safety_wit_5.
Axiom proof_of_is_pal_suffix_safety_wit_6 : is_pal_suffix_safety_wit_6.
Axiom proof_of_is_pal_suffix_safety_wit_7 : is_pal_suffix_safety_wit_7.
Axiom proof_of_is_pal_suffix_safety_wit_8 : is_pal_suffix_safety_wit_8.
Axiom proof_of_is_pal_suffix_safety_wit_9 : is_pal_suffix_safety_wit_9.
Axiom proof_of_is_pal_suffix_entail_wit_1 : is_pal_suffix_entail_wit_1.
Axiom proof_of_is_pal_suffix_entail_wit_2 : is_pal_suffix_entail_wit_2.
Axiom proof_of_is_pal_suffix_return_wit_1 : is_pal_suffix_return_wit_1.
Axiom proof_of_is_pal_suffix_return_wit_2 : is_pal_suffix_return_wit_2.
Axiom proof_of_is_pal_suffix_return_wit_3 : is_pal_suffix_return_wit_3.
Axiom proof_of_is_pal_suffix_partial_solve_wit_1 : is_pal_suffix_partial_solve_wit_1.
Axiom proof_of_is_pal_suffix_partial_solve_wit_2 : is_pal_suffix_partial_solve_wit_2.
Axiom proof_of_make_palindrome_safety_wit_1 : make_palindrome_safety_wit_1.
Axiom proof_of_make_palindrome_safety_wit_2 : make_palindrome_safety_wit_2.
Axiom proof_of_make_palindrome_safety_wit_3 : make_palindrome_safety_wit_3.
Axiom proof_of_make_palindrome_safety_wit_4 : make_palindrome_safety_wit_4.
Axiom proof_of_make_palindrome_safety_wit_5 : make_palindrome_safety_wit_5.
Axiom proof_of_make_palindrome_safety_wit_6 : make_palindrome_safety_wit_6.
Axiom proof_of_make_palindrome_safety_wit_7 : make_palindrome_safety_wit_7.
Axiom proof_of_make_palindrome_safety_wit_8 : make_palindrome_safety_wit_8.
Axiom proof_of_make_palindrome_safety_wit_9 : make_palindrome_safety_wit_9.
Axiom proof_of_make_palindrome_safety_wit_10 : make_palindrome_safety_wit_10.
Axiom proof_of_make_palindrome_safety_wit_11 : make_palindrome_safety_wit_11.
Axiom proof_of_make_palindrome_safety_wit_12 : make_palindrome_safety_wit_12.
Axiom proof_of_make_palindrome_safety_wit_13 : make_palindrome_safety_wit_13.
Axiom proof_of_make_palindrome_safety_wit_14 : make_palindrome_safety_wit_14.
Axiom proof_of_make_palindrome_safety_wit_15 : make_palindrome_safety_wit_15.
Axiom proof_of_make_palindrome_safety_wit_16 : make_palindrome_safety_wit_16.
Axiom proof_of_make_palindrome_safety_wit_17 : make_palindrome_safety_wit_17.
Axiom proof_of_make_palindrome_safety_wit_18 : make_palindrome_safety_wit_18.
Axiom proof_of_make_palindrome_safety_wit_19 : make_palindrome_safety_wit_19.
Axiom proof_of_make_palindrome_safety_wit_20 : make_palindrome_safety_wit_20.
Axiom proof_of_make_palindrome_safety_wit_21 : make_palindrome_safety_wit_21.
Axiom proof_of_make_palindrome_safety_wit_22 : make_palindrome_safety_wit_22.
Axiom proof_of_make_palindrome_safety_wit_23 : make_palindrome_safety_wit_23.
Axiom proof_of_make_palindrome_safety_wit_24 : make_palindrome_safety_wit_24.
Axiom proof_of_make_palindrome_safety_wit_25 : make_palindrome_safety_wit_25.
Axiom proof_of_make_palindrome_safety_wit_26 : make_palindrome_safety_wit_26.
Axiom proof_of_make_palindrome_safety_wit_27 : make_palindrome_safety_wit_27.
Axiom proof_of_make_palindrome_safety_wit_28 : make_palindrome_safety_wit_28.
Axiom proof_of_make_palindrome_safety_wit_29 : make_palindrome_safety_wit_29.
Axiom proof_of_make_palindrome_entail_wit_1 : make_palindrome_entail_wit_1.
Axiom proof_of_make_palindrome_entail_wit_2_1 : make_palindrome_entail_wit_2_1.
Axiom proof_of_make_palindrome_entail_wit_2_2 : make_palindrome_entail_wit_2_2.
Axiom proof_of_make_palindrome_entail_wit_2_3 : make_palindrome_entail_wit_2_3.
Axiom proof_of_make_palindrome_entail_wit_3_1 : make_palindrome_entail_wit_3_1.
Axiom proof_of_make_palindrome_entail_wit_3_2 : make_palindrome_entail_wit_3_2.
Axiom proof_of_make_palindrome_entail_wit_4 : make_palindrome_entail_wit_4.
Axiom proof_of_make_palindrome_entail_wit_5 : make_palindrome_entail_wit_5.
Axiom proof_of_make_palindrome_entail_wit_6 : make_palindrome_entail_wit_6.
Axiom proof_of_make_palindrome_entail_wit_7 : make_palindrome_entail_wit_7.
Axiom proof_of_make_palindrome_return_wit_1 : make_palindrome_return_wit_1.
Axiom proof_of_make_palindrome_partial_solve_wit_1 : make_palindrome_partial_solve_wit_1.
Axiom proof_of_make_palindrome_partial_solve_wit_2_pure : make_palindrome_partial_solve_wit_2_pure.
Axiom proof_of_make_palindrome_partial_solve_wit_2 : make_palindrome_partial_solve_wit_2.
Axiom proof_of_make_palindrome_partial_solve_wit_3_pure : make_palindrome_partial_solve_wit_3_pure.
Axiom proof_of_make_palindrome_partial_solve_wit_3 : make_palindrome_partial_solve_wit_3.
Axiom proof_of_make_palindrome_partial_solve_wit_4_pure : make_palindrome_partial_solve_wit_4_pure.
Axiom proof_of_make_palindrome_partial_solve_wit_4 : make_palindrome_partial_solve_wit_4.
Axiom proof_of_make_palindrome_partial_solve_wit_5 : make_palindrome_partial_solve_wit_5.
Axiom proof_of_make_palindrome_partial_solve_wit_6 : make_palindrome_partial_solve_wit_6.
Axiom proof_of_make_palindrome_partial_solve_wit_7 : make_palindrome_partial_solve_wit_7.
Axiom proof_of_make_palindrome_partial_solve_wit_8 : make_palindrome_partial_solve_wit_8.
Axiom proof_of_make_palindrome_partial_solve_wit_9 : make_palindrome_partial_solve_wit_9.

End VC_Correct.

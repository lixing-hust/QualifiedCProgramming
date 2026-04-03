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

(*----- Function pairs_sum_to_zero -----*)

Definition pairs_sum_to_zero_safety_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (lv: (@list Z)) ,
  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition pairs_sum_to_zero_safety_wit_2 := 
forall (l_size_pre: Z) (lv: (@list Z)) (l: Z) (i: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "l" ) )) # Ptr  |-> l)
  **  (IntArray.full l l_size_pre lv )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition pairs_sum_to_zero_safety_wit_3 := 
forall (l_size_pre: Z) (lv: (@list Z)) (l: Z) (i: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "l" ) )) # Ptr  |-> l)
  **  (IntArray.full l l_size_pre lv )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition pairs_sum_to_zero_safety_wit_4 := 
forall (l_size_pre: Z) (lv: (@list Z)) (i_2: Z) (l: Z) (j: Z) (i: Z) ,
  [| (j < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| forall (q_2: Z) , ((((i + 1 ) <= q_2) /\ (q_2 < j)) -> (((Znth (i) (lv) (0)) + (Znth (q_2) (lv) (0)) ) <> 0)) |] 
  &&  [| (i_2 < l_size_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= l_size_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i_2)) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "l" ) )) # Ptr  |-> l)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
|--
  [| (((Znth i lv 0) + (Znth j lv 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i lv 0) + (Znth j lv 0) )) |]
.

Definition pairs_sum_to_zero_safety_wit_5 := 
forall (l_size_pre: Z) (lv: (@list Z)) (i: Z) (l: Z) (j: Z) (i_2: Z) ,
  [| (j < l_size_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < l_size_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| forall (q_2: Z) , ((((i_2 + 1 ) <= q_2) /\ (q_2 < j)) -> (((Znth (i_2) (lv) (0)) + (Znth (q_2) (lv) (0)) ) <> 0)) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "l" ) )) # Ptr  |-> l)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition pairs_sum_to_zero_safety_wit_6 := 
forall (l_size_pre: Z) (lv: (@list Z)) (i: Z) (l: Z) (j: Z) (i_2: Z) ,
  [| (((Znth i_2 lv 0) + (Znth j lv 0) ) = 0) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < l_size_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| forall (q_2: Z) , ((((i_2 + 1 ) <= q_2) /\ (q_2 < j)) -> (((Znth (i_2) (lv) (0)) + (Znth (q_2) (lv) (0)) ) <> 0)) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "l" ) )) # Ptr  |-> l)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition pairs_sum_to_zero_safety_wit_7 := 
forall (l_size_pre: Z) (lv: (@list Z)) (i: Z) (l: Z) (j: Z) (i_2: Z) ,
  [| (((Znth i_2 lv 0) + (Znth j lv 0) ) <> 0) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < l_size_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| forall (q_2: Z) , ((((i_2 + 1 ) <= q_2) /\ (q_2 < j)) -> (((Znth (i_2) (lv) (0)) + (Znth (q_2) (lv) (0)) ) <> 0)) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "l" ) )) # Ptr  |-> l)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition pairs_sum_to_zero_safety_wit_8 := 
forall (l_size_pre: Z) (lv: (@list Z)) (i_2: Z) (l: Z) (j: Z) (i: Z) ,
  [| (j >= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| forall (q_2: Z) , ((((i + 1 ) <= q_2) /\ (q_2 < j)) -> (((Znth (i) (lv) (0)) + (Znth (q_2) (lv) (0)) ) <> 0)) |] 
  &&  [| (i_2 < l_size_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= l_size_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i_2)) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "l" ) )) # Ptr  |-> l)
  **  (IntArray.full l l_size_pre lv )
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition pairs_sum_to_zero_safety_wit_9 := 
forall (l_size_pre: Z) (lv: (@list Z)) (l: Z) (i: Z) ,
  [| (i >= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "l" ) )) # Ptr  |-> l)
  **  (IntArray.full l l_size_pre lv )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition pairs_sum_to_zero_entail_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (lv: (@list Z)) ,
  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l_pre l_size_pre lv )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < 0)) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l_pre l_size_pre lv )
.

Definition pairs_sum_to_zero_entail_wit_2 := 
forall (l_size_pre: Z) (lv: (@list Z)) (l: Z) (i: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
|--
  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= l_size_pre) |] 
  &&  [| forall (q_2: Z) , ((((i + 1 ) <= q_2) /\ (q_2 < (i + 1 ))) -> (((Znth (i) (lv) (0)) + (Znth (q_2) (lv) (0)) ) <> 0)) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
.

Definition pairs_sum_to_zero_entail_wit_3 := 
forall (l_size_pre: Z) (lv: (@list Z)) (i: Z) (l: Z) (j: Z) (i_2: Z) ,
  [| (((Znth i_2 lv 0) + (Znth j lv 0) ) <> 0) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < l_size_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| forall (q_2: Z) , ((((i_2 + 1 ) <= q_2) /\ (q_2 < j)) -> (((Znth (i_2) (lv) (0)) + (Znth (q_2) (lv) (0)) ) <> 0)) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
|--
  [| (0 <= i_2) |] 
  &&  [| (i_2 < l_size_pre) |] 
  &&  [| ((i_2 + 1 ) <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= l_size_pre) |] 
  &&  [| forall (q_2: Z) , ((((i_2 + 1 ) <= q_2) /\ (q_2 < (j + 1 ))) -> (((Znth (i_2) (lv) (0)) + (Znth (q_2) (lv) (0)) ) <> 0)) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
.

Definition pairs_sum_to_zero_entail_wit_4 := 
forall (l_size_pre: Z) (lv: (@list Z)) (i_2: Z) (l: Z) (j: Z) (i: Z) ,
  [| (j >= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| ((i + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| forall (q_2: Z) , ((((i + 1 ) <= q_2) /\ (q_2 < j)) -> (((Znth (i) (lv) (0)) + (Znth (q_2) (lv) (0)) ) <> 0)) |] 
  &&  [| (i_2 < l_size_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= l_size_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i_2)) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full l l_size_pre lv )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= l_size_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < (i + 1 ))) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
  **  ((( &( "j" ) )) # Int  |->_)
.

Definition pairs_sum_to_zero_return_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (lv: (@list Z)) (i: Z) (l: Z) (j: Z) (i_2: Z) ,
  [| (((Znth i_2 lv 0) + (Znth j lv 0) ) = 0) |] 
  &&  [| (j < l_size_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < l_size_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| forall (q_4: Z) , ((((i_2 + 1 ) <= q_4) /\ (q_4 < j)) -> (((Znth (i_2) (lv) (0)) + (Znth (q_4) (lv) (0)) ) <> 0)) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((0 <= p_3) /\ (p_3 < i)) /\ (p_3 < q_3)) /\ (q_3 < l_size_pre)) -> (((Znth (p_3) (lv) (0)) + (Znth (q_3) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
|--
  ([| (1 = 0) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |]
  &&  (IntArray.full l_pre l_size_pre lv ))
  ||
  (EX (q_2: Z)  (p_2: Z) ,
  [| (1 <> 0) |] 
  &&  [| (0 <= p_2) |] 
  &&  [| (p_2 < q_2) |] 
  &&  [| (q_2 < l_size_pre) |] 
  &&  [| (((Znth (p_2) (lv) (0)) + (Znth (q_2) (lv) (0)) ) = 0) |]
  &&  (IntArray.full l_pre l_size_pre lv ))
.

Definition pairs_sum_to_zero_return_wit_2 := 
forall (l_size_pre: Z) (l_pre: Z) (lv: (@list Z)) (l: Z) (i: Z) ,
  [| (i >= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (p_3: Z) , forall (q_3: Z) , (((((0 <= p_3) /\ (p_3 < i)) /\ (p_3 < q_3)) /\ (q_3 < l_size_pre)) -> (((Znth (p_3) (lv) (0)) + (Znth (q_3) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
|--
  ([| (0 = 0) |] 
  &&  [| forall (p: Z) , forall (q: Z) , ((((0 <= p) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |]
  &&  (IntArray.full l_pre l_size_pre lv ))
  ||
  (EX (q_2: Z)  (p_2: Z) ,
  [| (0 <> 0) |] 
  &&  [| (0 <= p_2) |] 
  &&  [| (p_2 < q_2) |] 
  &&  [| (q_2 < l_size_pre) |] 
  &&  [| (((Znth (p_2) (lv) (0)) + (Znth (q_2) (lv) (0)) ) = 0) |]
  &&  (IntArray.full l_pre l_size_pre lv ))
.

Definition pairs_sum_to_zero_partial_solve_wit_1 := 
forall (l_size_pre: Z) (lv: (@list Z)) (i: Z) (l: Z) (j: Z) (i_2: Z) ,
  [| (j < l_size_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < l_size_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| forall (q_2: Z) , ((((i_2 + 1 ) <= q_2) /\ (q_2 < j)) -> (((Znth (i_2) (lv) (0)) + (Znth (q_2) (lv) (0)) ) <> 0)) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
|--
  [| (j < l_size_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < l_size_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| forall (q_2: Z) , ((((i_2 + 1 ) <= q_2) /\ (q_2 < j)) -> (((Znth (i_2) (lv) (0)) + (Znth (q_2) (lv) (0)) ) <> 0)) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (((l + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 lv 0))
  **  (IntArray.missing_i l i_2 0 l_size_pre lv )
.

Definition pairs_sum_to_zero_partial_solve_wit_2 := 
forall (l_size_pre: Z) (lv: (@list Z)) (i: Z) (l: Z) (j: Z) (i_2: Z) ,
  [| (j < l_size_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < l_size_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| forall (q_2: Z) , ((((i_2 + 1 ) <= q_2) /\ (q_2 < j)) -> (((Znth (i_2) (lv) (0)) + (Znth (q_2) (lv) (0)) ) <> 0)) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
|--
  [| (j < l_size_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < l_size_pre) |] 
  &&  [| ((i_2 + 1 ) <= j) |] 
  &&  [| (j <= l_size_pre) |] 
  &&  [| forall (q_2: Z) , ((((i_2 + 1 ) <= q_2) /\ (q_2 < j)) -> (((Znth (i_2) (lv) (0)) + (Znth (q_2) (lv) (0)) ) <> 0)) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (p: Z) , forall (q: Z) , (((((0 <= p) /\ (p < i)) /\ (p < q)) /\ (q < l_size_pre)) -> (((Znth (p) (lv) (0)) + (Znth (q) (lv) (0)) ) <> 0)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (((l + (j * sizeof(INT) ) )) # Int  |-> (Znth j lv 0))
  **  (IntArray.missing_i l j 0 l_size_pre lv )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_pairs_sum_to_zero_safety_wit_1 : pairs_sum_to_zero_safety_wit_1.
Axiom proof_of_pairs_sum_to_zero_safety_wit_2 : pairs_sum_to_zero_safety_wit_2.
Axiom proof_of_pairs_sum_to_zero_safety_wit_3 : pairs_sum_to_zero_safety_wit_3.
Axiom proof_of_pairs_sum_to_zero_safety_wit_4 : pairs_sum_to_zero_safety_wit_4.
Axiom proof_of_pairs_sum_to_zero_safety_wit_5 : pairs_sum_to_zero_safety_wit_5.
Axiom proof_of_pairs_sum_to_zero_safety_wit_6 : pairs_sum_to_zero_safety_wit_6.
Axiom proof_of_pairs_sum_to_zero_safety_wit_7 : pairs_sum_to_zero_safety_wit_7.
Axiom proof_of_pairs_sum_to_zero_safety_wit_8 : pairs_sum_to_zero_safety_wit_8.
Axiom proof_of_pairs_sum_to_zero_safety_wit_9 : pairs_sum_to_zero_safety_wit_9.
Axiom proof_of_pairs_sum_to_zero_entail_wit_1 : pairs_sum_to_zero_entail_wit_1.
Axiom proof_of_pairs_sum_to_zero_entail_wit_2 : pairs_sum_to_zero_entail_wit_2.
Axiom proof_of_pairs_sum_to_zero_entail_wit_3 : pairs_sum_to_zero_entail_wit_3.
Axiom proof_of_pairs_sum_to_zero_entail_wit_4 : pairs_sum_to_zero_entail_wit_4.
Axiom proof_of_pairs_sum_to_zero_return_wit_1 : pairs_sum_to_zero_return_wit_1.
Axiom proof_of_pairs_sum_to_zero_return_wit_2 : pairs_sum_to_zero_return_wit_2.
Axiom proof_of_pairs_sum_to_zero_partial_solve_wit_1 : pairs_sum_to_zero_partial_solve_wit_1.
Axiom proof_of_pairs_sum_to_zero_partial_solve_wit_2 : pairs_sum_to_zero_partial_solve_wit_2.

End VC_Correct.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
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
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_91.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function is_bored -----*)

Definition is_bored_safety_wit_1 := 
forall (S_pre: Z) (input: (@list Z)) (PreH1 : (valid_string input )) (PreH2 : (problem_91_pre_z input )) (PreH3 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "isstart" ) )) # Int  |->_)
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  (store_string S_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_bored_safety_wit_2 := 
forall (S_pre: Z) (input: (@list Z)) (PreH1 : (valid_string input )) (PreH2 : (problem_91_pre_z input )) (PreH3 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "isi" ) )) # Int  |->_)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  (store_string S_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_bored_safety_wit_3 := 
forall (S_pre: Z) (input: (@list Z)) (PreH1 : (valid_string input )) (PreH2 : (problem_91_pre_z input )) (PreH3 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  (store_string S_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_bored_safety_wit_4 := 
forall (S_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_91_pre_z input )) (PreH5 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (store_string S_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_bored_safety_wit_5 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_91_pre_z input )) (PreH5 : ((string_length (input)) < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH9 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH10 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH11 : (0 <= sum)) (PreH12 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
  **  (store_string S_pre input )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition is_bored_safety_wit_6 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 32)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (valid_string input )) (PreH5 : (problem_91_pre_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH10 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH11 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH12 : (0 <= sum)) (PreH13 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
  **  (store_string S_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_bored_safety_wit_7 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (isi = 1)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (valid_string input )) (PreH6 : (problem_91_pre_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH11 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH12 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH13 : (0 <= sum)) (PreH14 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
  **  (store_string S_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_bored_safety_wit_8 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (isi = 1)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (valid_string input )) (PreH6 : (problem_91_pre_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH11 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH12 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH13 : (0 <= sum)) (PreH14 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ ((sum + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + 1 )) ”
.

Definition is_bored_safety_wit_9 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (isi = 1)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (valid_string input )) (PreH6 : (problem_91_pre_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH11 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH12 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH13 : (0 <= sum)) (PreH14 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_bored_safety_wit_10 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (isi = 1)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (valid_string input )) (PreH6 : (problem_91_pre_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH11 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH12 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH13 : (0 <= sum)) (PreH14 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (73 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 73) ”
.

Definition is_bored_safety_wit_11 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 32)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (valid_string input )) (PreH5 : (problem_91_pre_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH10 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH11 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH12 : (0 <= sum)) (PreH13 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
  **  (store_string S_pre input )
|--
  “ (73 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 73) ”
.

Definition is_bored_safety_wit_12 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (isi <> 1)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (valid_string input )) (PreH6 : (problem_91_pre_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH11 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH12 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH13 : (0 <= sum)) (PreH14 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
  **  (store_string S_pre input )
|--
  “ (73 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 73) ”
.

Definition is_bored_safety_wit_13 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 73)) (PreH2 : (isi = 1)) (PreH3 : ((Znth i (c_string (input)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (valid_string input )) (PreH7 : (problem_91_pre_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH12 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH13 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ False ”
.

Definition is_bored_safety_wit_14 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 73)) (PreH2 : (isi <> 1)) (PreH3 : ((Znth i (c_string (input)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (valid_string input )) (PreH7 : (problem_91_pre_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH12 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH13 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
  **  (store_string S_pre input )
|--
  “ False ”
.

Definition is_bored_safety_wit_15 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 73)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (valid_string input )) (PreH6 : (problem_91_pre_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH11 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH12 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH13 : (0 <= sum)) (PreH14 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
  **  (store_string S_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_bored_safety_wit_16 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (isstart = 1)) (PreH2 : ((Znth i (c_string (input)) 0) = 73)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (valid_string input )) (PreH7 : (problem_91_pre_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH12 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH13 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
  **  (store_string S_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_bored_safety_wit_17 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 73)) (PreH2 : (isi <> 1)) (PreH3 : ((Znth i (c_string (input)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (valid_string input )) (PreH7 : (problem_91_pre_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH12 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH13 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
  **  (store_string S_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_bored_safety_wit_18 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 73)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (valid_string input )) (PreH6 : (problem_91_pre_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH11 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH12 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH13 : (0 <= sum)) (PreH14 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
  **  (store_string S_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_bored_safety_wit_19 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 73)) (PreH2 : (isi = 1)) (PreH3 : ((Znth i (c_string (input)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (valid_string input )) (PreH7 : (problem_91_pre_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH12 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH13 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_bored_safety_wit_20 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (isstart <> 1)) (PreH2 : ((Znth i (c_string (input)) 0) = 73)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (valid_string input )) (PreH7 : (problem_91_pre_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH12 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH13 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
  **  (store_string S_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_bored_safety_wit_21 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (isstart = 1)) (PreH2 : ((Znth i (c_string (input)) 0) = 73)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (valid_string input )) (PreH7 : (problem_91_pre_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH12 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH13 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 1)
  **  (store_string S_pre input )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition is_bored_safety_wit_22 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 73)) (PreH2 : (isi <> 1)) (PreH3 : ((Znth i (c_string (input)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (valid_string input )) (PreH7 : (problem_91_pre_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH12 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH13 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition is_bored_safety_wit_23 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 73)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (input)))) (PreH5 : (valid_string input )) (PreH6 : (problem_91_pre_z input )) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH11 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH12 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH13 : (0 <= sum)) (PreH14 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition is_bored_safety_wit_24 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 73)) (PreH2 : (isi = 1)) (PreH3 : ((Znth i (c_string (input)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (valid_string input )) (PreH7 : (problem_91_pre_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH12 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH13 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition is_bored_safety_wit_25 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (isstart <> 1)) (PreH2 : ((Znth i (c_string (input)) 0) = 73)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (valid_string input )) (PreH7 : (problem_91_pre_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH12 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH13 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition is_bored_safety_wit_26 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 32)) (PreH2 : (isstart = 1)) (PreH3 : ((Znth i (c_string (input)) 0) = 73)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (valid_string input )) (PreH8 : (problem_91_pre_z input )) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH13 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH14 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH15 : (0 <= sum)) (PreH16 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 1)
  **  (store_string S_pre input )
|--
  “ False ”
.

Definition is_bored_safety_wit_27 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 32)) (PreH2 : ((Znth i (c_string (input)) 0) <> 73)) (PreH3 : (isi <> 1)) (PreH4 : ((Znth i (c_string (input)) 0) = 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (valid_string input )) (PreH8 : (problem_91_pre_z input )) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH13 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH14 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH15 : (0 <= sum)) (PreH16 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ False ”
.

Definition is_bored_safety_wit_28 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 32)) (PreH2 : ((Znth i (c_string (input)) 0) <> 73)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (valid_string input )) (PreH7 : (problem_91_pre_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH12 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH13 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ False ”
.

Definition is_bored_safety_wit_29 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 32)) (PreH2 : ((Znth i (c_string (input)) 0) <> 73)) (PreH3 : (isi = 1)) (PreH4 : ((Znth i (c_string (input)) 0) = 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (valid_string input )) (PreH8 : (problem_91_pre_z input )) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH13 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH14 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH15 : (0 <= sum)) (PreH16 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ False ”
.

Definition is_bored_safety_wit_30 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 32)) (PreH2 : (isstart <> 1)) (PreH3 : ((Znth i (c_string (input)) 0) = 73)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (valid_string input )) (PreH8 : (problem_91_pre_z input )) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH13 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH14 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH15 : (0 <= sum)) (PreH16 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ False ”
.

Definition is_bored_safety_wit_31 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 32)) (PreH2 : (isstart = 1)) (PreH3 : ((Znth i (c_string (input)) 0) = 73)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (valid_string input )) (PreH8 : (problem_91_pre_z input )) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH13 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH14 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH15 : (0 <= sum)) (PreH16 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 1)
  **  (store_string S_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_bored_safety_wit_32 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 32)) (PreH2 : ((Znth i (c_string (input)) 0) <> 73)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (valid_string input )) (PreH7 : (problem_91_pre_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH12 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH13 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_bored_safety_wit_33 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 32)) (PreH2 : (isstart <> 1)) (PreH3 : ((Znth i (c_string (input)) 0) = 73)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (valid_string input )) (PreH8 : (problem_91_pre_z input )) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH13 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH14 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH15 : (0 <= sum)) (PreH16 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_bored_safety_wit_34 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 32)) (PreH2 : (isstart = 1)) (PreH3 : ((Znth i (c_string (input)) 0) = 73)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (valid_string input )) (PreH8 : (problem_91_pre_z input )) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH13 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH14 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH15 : (0 <= sum)) (PreH16 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
  **  (store_string S_pre input )
|--
  “ (46 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 46) ”
.

Definition is_bored_safety_wit_35 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 32)) (PreH2 : ((Znth i (c_string (input)) 0) <> 73)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (input)))) (PreH6 : (valid_string input )) (PreH7 : (problem_91_pre_z input )) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH12 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH13 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (46 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 46) ”
.

Definition is_bored_safety_wit_36 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 32)) (PreH2 : (isstart <> 1)) (PreH3 : ((Znth i (c_string (input)) 0) = 73)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (valid_string input )) (PreH8 : (problem_91_pre_z input )) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH13 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH14 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH15 : (0 <= sum)) (PreH16 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (46 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 46) ”
.

Definition is_bored_safety_wit_37 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 32)) (PreH2 : ((Znth i (c_string (input)) 0) <> 73)) (PreH3 : (isi <> 1)) (PreH4 : ((Znth i (c_string (input)) 0) = 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (valid_string input )) (PreH8 : (problem_91_pre_z input )) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH13 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH14 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH15 : (0 <= sum)) (PreH16 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (46 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 46) ”
.

Definition is_bored_safety_wit_38 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 32)) (PreH2 : ((Znth i (c_string (input)) 0) <> 73)) (PreH3 : (isi = 1)) (PreH4 : ((Znth i (c_string (input)) 0) = 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (valid_string input )) (PreH8 : (problem_91_pre_z input )) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH13 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH14 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH15 : (0 <= sum)) (PreH16 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (46 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 46) ”
.

Definition is_bored_safety_wit_39 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 46)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : (isstart = 1)) (PreH4 : ((Znth i (c_string (input)) 0) = 73)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (valid_string input )) (PreH9 : (problem_91_pre_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH14 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH15 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH16 : (0 <= sum)) (PreH17 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
  **  (store_string S_pre input )
|--
  “ False ”
.

Definition is_bored_safety_wit_40 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 46)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : (isstart <> 1)) (PreH4 : ((Znth i (c_string (input)) 0) = 73)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (valid_string input )) (PreH9 : (problem_91_pre_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH14 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH15 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH16 : (0 <= sum)) (PreH17 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ False ”
.

Definition is_bored_safety_wit_41 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 46)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : ((Znth i (c_string (input)) 0) <> 73)) (PreH4 : (isi <> 1)) (PreH5 : ((Znth i (c_string (input)) 0) = 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (valid_string input )) (PreH9 : (problem_91_pre_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH14 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH15 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH16 : (0 <= sum)) (PreH17 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ False ”
.

Definition is_bored_safety_wit_42 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 46)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : ((Znth i (c_string (input)) 0) <> 73)) (PreH4 : (isi = 1)) (PreH5 : ((Znth i (c_string (input)) 0) = 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (valid_string input )) (PreH9 : (problem_91_pre_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH14 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH15 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH16 : (0 <= sum)) (PreH17 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ False ”
.

Definition is_bored_safety_wit_43 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 46)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : ((Znth i (c_string (input)) 0) <> 73)) (PreH4 : (isi = 1)) (PreH5 : ((Znth i (c_string (input)) 0) = 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (valid_string input )) (PreH9 : (problem_91_pre_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH14 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH15 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH16 : (0 <= sum)) (PreH17 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition is_bored_safety_wit_44 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 46)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : ((Znth i (c_string (input)) 0) <> 73)) (PreH4 : (isi <> 1)) (PreH5 : ((Znth i (c_string (input)) 0) = 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (valid_string input )) (PreH9 : (problem_91_pre_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH14 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH15 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH16 : (0 <= sum)) (PreH17 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition is_bored_safety_wit_45 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 46)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : (isstart <> 1)) (PreH4 : ((Znth i (c_string (input)) 0) = 73)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (valid_string input )) (PreH9 : (problem_91_pre_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH14 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH15 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH16 : (0 <= sum)) (PreH17 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition is_bored_safety_wit_46 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 46)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : ((Znth i (c_string (input)) 0) <> 73)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (valid_string input )) (PreH8 : (problem_91_pre_z input )) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH13 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH14 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH15 : (0 <= sum)) (PreH16 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition is_bored_safety_wit_47 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 46)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : (isstart = 1)) (PreH4 : ((Znth i (c_string (input)) 0) = 73)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (valid_string input )) (PreH9 : (problem_91_pre_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH14 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH15 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH16 : (0 <= sum)) (PreH17 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
  **  (store_string S_pre input )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition is_bored_safety_wit_48 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 63)) (PreH2 : ((Znth i (c_string (input)) 0) <> 46)) (PreH3 : ((Znth i (c_string (input)) 0) = 32)) (PreH4 : ((Znth i (c_string (input)) 0) <> 73)) (PreH5 : (isi = 1)) (PreH6 : ((Znth i (c_string (input)) 0) = 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (valid_string input )) (PreH10 : (problem_91_pre_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH15 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH16 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH17 : (0 <= sum)) (PreH18 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ False ”
.

Definition is_bored_safety_wit_49 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 63)) (PreH2 : ((Znth i (c_string (input)) 0) <> 46)) (PreH3 : ((Znth i (c_string (input)) 0) = 32)) (PreH4 : ((Znth i (c_string (input)) 0) <> 73)) (PreH5 : (isi <> 1)) (PreH6 : ((Znth i (c_string (input)) 0) = 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (valid_string input )) (PreH10 : (problem_91_pre_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH15 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH16 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH17 : (0 <= sum)) (PreH18 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ False ”
.

Definition is_bored_safety_wit_50 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 63)) (PreH2 : ((Znth i (c_string (input)) 0) <> 46)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (isstart <> 1)) (PreH5 : ((Znth i (c_string (input)) 0) = 73)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (valid_string input )) (PreH10 : (problem_91_pre_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH15 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH16 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH17 : (0 <= sum)) (PreH18 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ False ”
.

Definition is_bored_safety_wit_51 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 63)) (PreH2 : ((Znth i (c_string (input)) 0) <> 46)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (isstart = 1)) (PreH5 : ((Znth i (c_string (input)) 0) = 73)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (valid_string input )) (PreH10 : (problem_91_pre_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH15 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH16 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH17 : (0 <= sum)) (PreH18 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
  **  (store_string S_pre input )
|--
  “ False ”
.

Definition is_bored_safety_wit_52 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 63)) (PreH2 : ((Znth i (c_string (input)) 0) <> 46)) (PreH3 : ((Znth i (c_string (input)) 0) = 32)) (PreH4 : ((Znth i (c_string (input)) 0) <> 73)) (PreH5 : (isi = 1)) (PreH6 : ((Znth i (c_string (input)) 0) = 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (valid_string input )) (PreH10 : (problem_91_pre_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH15 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH16 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH17 : (0 <= sum)) (PreH18 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (33 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 33) ”
.

Definition is_bored_safety_wit_53 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 63)) (PreH2 : ((Znth i (c_string (input)) 0) <> 46)) (PreH3 : ((Znth i (c_string (input)) 0) = 32)) (PreH4 : ((Znth i (c_string (input)) 0) <> 73)) (PreH5 : (isi <> 1)) (PreH6 : ((Znth i (c_string (input)) 0) = 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (valid_string input )) (PreH10 : (problem_91_pre_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH15 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH16 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH17 : (0 <= sum)) (PreH18 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (33 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 33) ”
.

Definition is_bored_safety_wit_54 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 63)) (PreH2 : ((Znth i (c_string (input)) 0) <> 46)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (isstart <> 1)) (PreH5 : ((Znth i (c_string (input)) 0) = 73)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (valid_string input )) (PreH10 : (problem_91_pre_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH15 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH16 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH17 : (0 <= sum)) (PreH18 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (33 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 33) ”
.

Definition is_bored_safety_wit_55 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 63)) (PreH2 : ((Znth i (c_string (input)) 0) <> 46)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : ((Znth i (c_string (input)) 0) <> 73)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (valid_string input )) (PreH9 : (problem_91_pre_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH14 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH15 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH16 : (0 <= sum)) (PreH17 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (33 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 33) ”
.

Definition is_bored_safety_wit_56 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 63)) (PreH2 : ((Znth i (c_string (input)) 0) <> 46)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (isstart = 1)) (PreH5 : ((Znth i (c_string (input)) 0) = 73)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (valid_string input )) (PreH10 : (problem_91_pre_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH15 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH16 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH17 : (0 <= sum)) (PreH18 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
  **  (store_string S_pre input )
|--
  “ (33 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 33) ”
.

Definition is_bored_safety_wit_57 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 33)) (PreH2 : ((Znth i (c_string (input)) 0) <> 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) = 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 73)) (PreH6 : (isi = 1)) (PreH7 : ((Znth i (c_string (input)) 0) = 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ False ”
.

Definition is_bored_safety_wit_58 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 33)) (PreH2 : ((Znth i (c_string (input)) 0) <> 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) = 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 73)) (PreH6 : (isi <> 1)) (PreH7 : ((Znth i (c_string (input)) 0) = 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ False ”
.

Definition is_bored_safety_wit_59 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 33)) (PreH2 : ((Znth i (c_string (input)) 0) <> 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (isstart <> 1)) (PreH6 : ((Znth i (c_string (input)) 0) = 73)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ False ”
.

Definition is_bored_safety_wit_60 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 33)) (PreH2 : ((Znth i (c_string (input)) 0) <> 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (isstart = 1)) (PreH6 : ((Znth i (c_string (input)) 0) = 73)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
  **  (store_string S_pre input )
|--
  “ False ”
.

Definition is_bored_safety_wit_61 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 63)) (PreH2 : ((Znth i (c_string (input)) 0) <> 46)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : ((Znth i (c_string (input)) 0) <> 73)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (valid_string input )) (PreH9 : (problem_91_pre_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH14 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH15 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH16 : (0 <= sum)) (PreH17 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_bored_safety_wit_62 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 46)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : ((Znth i (c_string (input)) 0) <> 73)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (valid_string input )) (PreH8 : (problem_91_pre_z input )) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH13 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH14 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH15 : (0 <= sum)) (PreH16 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_bored_safety_wit_63 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 33)) (PreH2 : ((Znth i (c_string (input)) 0) <> 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 73)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (valid_string input )) (PreH10 : (problem_91_pre_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH15 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH16 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH17 : (0 <= sum)) (PreH18 : (sum <= i)) ,
  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_bored_safety_wit_64 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 63)) (PreH2 : ((Znth i (c_string (input)) 0) <> 46)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : ((Znth i (c_string (input)) 0) <> 73)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (valid_string input )) (PreH9 : (problem_91_pre_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH14 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH15 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH16 : (0 <= sum)) (PreH17 : (sum <= i)) ,
  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition is_bored_safety_wit_65 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 46)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : ((Znth i (c_string (input)) 0) <> 73)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (valid_string input )) (PreH8 : (problem_91_pre_z input )) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH13 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH14 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH15 : (0 <= sum)) (PreH16 : (sum <= i)) ,
  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition is_bored_safety_wit_66 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 33)) (PreH2 : ((Znth i (c_string (input)) 0) <> 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 73)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (valid_string input )) (PreH10 : (problem_91_pre_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH15 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH16 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH17 : (0 <= sum)) (PreH18 : (sum <= i)) ,
  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition is_bored_safety_wit_67 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 33)) (PreH2 : ((Znth i (c_string (input)) 0) <> 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (isstart = 1)) (PreH6 : ((Znth i (c_string (input)) 0) = 73)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
  **  (store_string S_pre input )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition is_bored_safety_wit_68 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 33)) (PreH2 : ((Znth i (c_string (input)) 0) <> 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 73)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (valid_string input )) (PreH10 : (problem_91_pre_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH15 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH16 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH17 : (0 <= sum)) (PreH18 : (sum <= i)) ,
  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition is_bored_safety_wit_69 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 33)) (PreH2 : ((Znth i (c_string (input)) 0) <> 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (isstart <> 1)) (PreH6 : ((Znth i (c_string (input)) 0) = 73)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition is_bored_safety_wit_70 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 33)) (PreH2 : ((Znth i (c_string (input)) 0) <> 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) = 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 73)) (PreH6 : (isi <> 1)) (PreH7 : ((Znth i (c_string (input)) 0) = 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition is_bored_safety_wit_71 := 
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 33)) (PreH2 : ((Znth i (c_string (input)) 0) <> 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) = 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 73)) (PreH6 : (isi = 1)) (PreH7 : ((Znth i (c_string (input)) 0) = 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  (store_string S_pre input )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition is_bored_entail_wit_1 := 
(
forall (S_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_91_pre_z input )) (PreH5 : ((string_length (input)) < INT_MAX)) ,
  (store_string S_pre input )
|--
  “ (retval = (string_length (input))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_91_pre_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (0 = (bored_sum_prefix_z (0) (input))) ” 
  &&  “ (1 = (bored_isstart_prefix_z (0) (input))) ” 
  &&  “ (0 = (bored_isi_prefix_z (0) (input))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ”
  &&  (store_string S_pre input )
) \/
(
forall (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_91_pre_z input )) (PreH5 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (bored_isi_prefix_z (0) (input))) ” 
  &&  “ (1 = (bored_isstart_prefix_z (0) (input))) ” 
  &&  “ (0 = (bored_sum_prefix_z (0) (input))) ” 
  &&  “ (0 <= retval) ”
  &&  emp
).

Definition is_bored_entail_wit_1_split_goal_1 := 
forall (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_91_pre_z input )) (PreH5 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (bored_isi_prefix_z (0) (input))) ”
.

Definition is_bored_entail_wit_1_split_goal_2 := 
forall (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_91_pre_z input )) (PreH5 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (bored_isstart_prefix_z (0) (input))) ”
.

Definition is_bored_entail_wit_1_split_goal_3 := 
forall (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_91_pre_z input )) (PreH5 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (bored_sum_prefix_z (0) (input))) ”
.

Definition is_bored_entail_wit_1_split_goal_4 := 
forall (input: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : (problem_91_pre_z input )) (PreH5 : ((string_length (input)) < INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= retval) ”
.

Definition is_bored_entail_wit_2_1 := 
(
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 63)) (PreH2 : ((Znth i (c_string (input)) 0) <> 46)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : ((Znth i (c_string (input)) 0) <> 73)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (valid_string input )) (PreH9 : (problem_91_pre_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH14 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH15 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH16 : (0 <= sum)) (PreH17 : (sum <= i)) ,
  (store_string S_pre input )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_91_pre_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (1 = (bored_isstart_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (i + 1 )) ”
  &&  (store_string S_pre input )
) \/
(
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) = 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 73)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (valid_string input )) (PreH10 : (problem_91_pre_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH15 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH16 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH17 : (0 <= sum)) (PreH18 : (sum <= i)) ,
  TT && emp 
|--
  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (1 = (bored_isstart_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ”
  &&  emp
).

Definition is_bored_entail_wit_2_1_split_goal_1 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) = 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 73)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (valid_string input )) (PreH10 : (problem_91_pre_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH15 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH16 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH17 : (0 <= sum)) (PreH18 : (sum <= i)) ,
  TT && emp 
|--
  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_1_split_goal_2 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) = 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 73)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (valid_string input )) (PreH10 : (problem_91_pre_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH15 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH16 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH17 : (0 <= sum)) (PreH18 : (sum <= i)) ,
  TT && emp 
|--
  “ (1 = (bored_isstart_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_1_split_goal_3 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) = 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 73)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (valid_string input )) (PreH10 : (problem_91_pre_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH15 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH16 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH17 : (0 <= sum)) (PreH18 : (sum <= i)) ,
  TT && emp 
|--
  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_2 := 
(
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 46)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : ((Znth i (c_string (input)) 0) <> 73)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (input)))) (PreH7 : (valid_string input )) (PreH8 : (problem_91_pre_z input )) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH13 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH14 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH15 : (0 <= sum)) (PreH16 : (sum <= i)) ,
  (store_string S_pre input )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_91_pre_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (1 = (bored_isstart_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (i + 1 )) ”
  &&  (store_string S_pre input )
) \/
(
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) = 46)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : ((Znth i (c_string (input)) 0) <> 73)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (valid_string input )) (PreH9 : (problem_91_pre_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH14 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH15 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH16 : (0 <= sum)) (PreH17 : (sum <= i)) ,
  TT && emp 
|--
  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (1 = (bored_isstart_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ”
  &&  emp
).

Definition is_bored_entail_wit_2_2_split_goal_1 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) = 46)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : ((Znth i (c_string (input)) 0) <> 73)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (valid_string input )) (PreH9 : (problem_91_pre_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH14 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH15 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH16 : (0 <= sum)) (PreH17 : (sum <= i)) ,
  TT && emp 
|--
  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_2_split_goal_2 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) = 46)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : ((Znth i (c_string (input)) 0) <> 73)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (valid_string input )) (PreH9 : (problem_91_pre_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH14 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH15 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH16 : (0 <= sum)) (PreH17 : (sum <= i)) ,
  TT && emp 
|--
  “ (1 = (bored_isstart_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_2_split_goal_3 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) = 46)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : ((Znth i (c_string (input)) 0) <> 73)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (n = (string_length (input)))) (PreH8 : (valid_string input )) (PreH9 : (problem_91_pre_z input )) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH14 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH15 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH16 : (0 <= sum)) (PreH17 : (sum <= i)) ,
  TT && emp 
|--
  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_3 := 
(
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 33)) (PreH2 : ((Znth i (c_string (input)) 0) <> 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 73)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (valid_string input )) (PreH10 : (problem_91_pre_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH15 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH16 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH17 : (0 <= sum)) (PreH18 : (sum <= i)) ,
  (store_string S_pre input )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_91_pre_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (1 = (bored_isstart_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (i + 1 )) ”
  &&  (store_string S_pre input )
) \/
(
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) = 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 73)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  TT && emp 
|--
  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (1 = (bored_isstart_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ”
  &&  emp
).

Definition is_bored_entail_wit_2_3_split_goal_1 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) = 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 73)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  TT && emp 
|--
  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_3_split_goal_2 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) = 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 73)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  TT && emp 
|--
  “ (1 = (bored_isstart_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_3_split_goal_3 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) = 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 73)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  TT && emp 
|--
  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_4 := 
(
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 33)) (PreH2 : ((Znth i (c_string (input)) 0) <> 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (isstart = 1)) (PreH6 : ((Znth i (c_string (input)) 0) = 73)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  (store_string S_pre input )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_91_pre_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 = (bored_isstart_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (1 = (bored_isi_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (i + 1 )) ”
  &&  (store_string S_pre input )
) \/
(
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (isstart = 1)) (PreH7 : ((Znth i (c_string (input)) 0) = 73)) (PreH8 : ((Znth i (c_string (input)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (n = (string_length (input)))) (PreH11 : (valid_string input )) (PreH12 : (problem_91_pre_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH17 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH18 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH19 : (0 <= sum)) (PreH20 : (sum <= i)) ,
  TT && emp 
|--
  “ (1 = (bored_isi_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 = (bored_isstart_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ”
  &&  emp
).

Definition is_bored_entail_wit_2_4_split_goal_1 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (isstart = 1)) (PreH7 : ((Znth i (c_string (input)) 0) = 73)) (PreH8 : ((Znth i (c_string (input)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (n = (string_length (input)))) (PreH11 : (valid_string input )) (PreH12 : (problem_91_pre_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH17 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH18 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH19 : (0 <= sum)) (PreH20 : (sum <= i)) ,
  TT && emp 
|--
  “ (1 = (bored_isi_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_4_split_goal_2 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (isstart = 1)) (PreH7 : ((Znth i (c_string (input)) 0) = 73)) (PreH8 : ((Znth i (c_string (input)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (n = (string_length (input)))) (PreH11 : (valid_string input )) (PreH12 : (problem_91_pre_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH17 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH18 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH19 : (0 <= sum)) (PreH20 : (sum <= i)) ,
  TT && emp 
|--
  “ (0 = (bored_isstart_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_4_split_goal_3 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (isstart = 1)) (PreH7 : ((Znth i (c_string (input)) 0) = 73)) (PreH8 : ((Znth i (c_string (input)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (n = (string_length (input)))) (PreH11 : (valid_string input )) (PreH12 : (problem_91_pre_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH17 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH18 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH19 : (0 <= sum)) (PreH20 : (sum <= i)) ,
  TT && emp 
|--
  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_5 := 
(
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 33)) (PreH2 : ((Znth i (c_string (input)) 0) <> 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 73)) (PreH6 : ((Znth i (c_string (input)) 0) <> 32)) (PreH7 : (i < n)) (PreH8 : (n = (string_length (input)))) (PreH9 : (valid_string input )) (PreH10 : (problem_91_pre_z input )) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH15 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH16 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH17 : (0 <= sum)) (PreH18 : (sum <= i)) ,
  (store_string S_pre input )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_91_pre_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 = (bored_isstart_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (i + 1 )) ”
  &&  (store_string S_pre input )
) \/
(
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 73)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  TT && emp 
|--
  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 = (bored_isstart_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ”
  &&  emp
).

Definition is_bored_entail_wit_2_5_split_goal_1 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 73)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  TT && emp 
|--
  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_5_split_goal_2 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 73)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  TT && emp 
|--
  “ (0 = (bored_isstart_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_5_split_goal_3 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 73)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  TT && emp 
|--
  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_6 := 
(
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 33)) (PreH2 : ((Znth i (c_string (input)) 0) <> 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (isstart <> 1)) (PreH6 : ((Znth i (c_string (input)) 0) = 73)) (PreH7 : ((Znth i (c_string (input)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  (store_string S_pre input )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_91_pre_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 = (bored_isstart_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (i + 1 )) ”
  &&  (store_string S_pre input )
) \/
(
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (isstart <> 1)) (PreH7 : ((Znth i (c_string (input)) 0) = 73)) (PreH8 : ((Znth i (c_string (input)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (n = (string_length (input)))) (PreH11 : (valid_string input )) (PreH12 : (problem_91_pre_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH17 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH18 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH19 : (0 <= sum)) (PreH20 : (sum <= i)) ,
  TT && emp 
|--
  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 = (bored_isstart_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ”
  &&  emp
).

Definition is_bored_entail_wit_2_6_split_goal_1 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (isstart <> 1)) (PreH7 : ((Znth i (c_string (input)) 0) = 73)) (PreH8 : ((Znth i (c_string (input)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (n = (string_length (input)))) (PreH11 : (valid_string input )) (PreH12 : (problem_91_pre_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH17 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH18 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH19 : (0 <= sum)) (PreH20 : (sum <= i)) ,
  TT && emp 
|--
  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_6_split_goal_2 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (isstart <> 1)) (PreH7 : ((Znth i (c_string (input)) 0) = 73)) (PreH8 : ((Znth i (c_string (input)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (n = (string_length (input)))) (PreH11 : (valid_string input )) (PreH12 : (problem_91_pre_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH17 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH18 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH19 : (0 <= sum)) (PreH20 : (sum <= i)) ,
  TT && emp 
|--
  “ (0 = (bored_isstart_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_6_split_goal_3 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (isstart <> 1)) (PreH7 : ((Znth i (c_string (input)) 0) = 73)) (PreH8 : ((Znth i (c_string (input)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (n = (string_length (input)))) (PreH11 : (valid_string input )) (PreH12 : (problem_91_pre_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH17 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH18 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH19 : (0 <= sum)) (PreH20 : (sum <= i)) ,
  TT && emp 
|--
  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_7 := 
(
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 33)) (PreH2 : ((Znth i (c_string (input)) 0) <> 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) = 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 73)) (PreH6 : (isi <> 1)) (PreH7 : ((Znth i (c_string (input)) 0) = 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  (store_string S_pre input )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_91_pre_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (isstart = (bored_isstart_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (i + 1 )) ”
  &&  (store_string S_pre input )
) \/
(
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) = 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 73)) (PreH7 : (isi <> 1)) (PreH8 : ((Znth i (c_string (input)) 0) = 32)) (PreH9 : (i < n)) (PreH10 : (n = (string_length (input)))) (PreH11 : (valid_string input )) (PreH12 : (problem_91_pre_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH17 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH18 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH19 : (0 <= sum)) (PreH20 : (sum <= i)) ,
  TT && emp 
|--
  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (isstart = (bored_isstart_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ”
  &&  emp
).

Definition is_bored_entail_wit_2_7_split_goal_1 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) = 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 73)) (PreH7 : (isi <> 1)) (PreH8 : ((Znth i (c_string (input)) 0) = 32)) (PreH9 : (i < n)) (PreH10 : (n = (string_length (input)))) (PreH11 : (valid_string input )) (PreH12 : (problem_91_pre_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH17 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH18 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH19 : (0 <= sum)) (PreH20 : (sum <= i)) ,
  TT && emp 
|--
  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_7_split_goal_2 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) = 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 73)) (PreH7 : (isi <> 1)) (PreH8 : ((Znth i (c_string (input)) 0) = 32)) (PreH9 : (i < n)) (PreH10 : (n = (string_length (input)))) (PreH11 : (valid_string input )) (PreH12 : (problem_91_pre_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH17 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH18 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH19 : (0 <= sum)) (PreH20 : (sum <= i)) ,
  TT && emp 
|--
  “ (isstart = (bored_isstart_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_7_split_goal_3 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) = 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 73)) (PreH7 : (isi <> 1)) (PreH8 : ((Znth i (c_string (input)) 0) = 32)) (PreH9 : (i < n)) (PreH10 : (n = (string_length (input)))) (PreH11 : (valid_string input )) (PreH12 : (problem_91_pre_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH17 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH18 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH19 : (0 <= sum)) (PreH20 : (sum <= i)) ,
  TT && emp 
|--
  “ (sum = (bored_sum_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_8 := 
(
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 33)) (PreH2 : ((Znth i (c_string (input)) 0) <> 63)) (PreH3 : ((Znth i (c_string (input)) 0) <> 46)) (PreH4 : ((Znth i (c_string (input)) 0) = 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 73)) (PreH6 : (isi = 1)) (PreH7 : ((Znth i (c_string (input)) 0) = 32)) (PreH8 : (i < n)) (PreH9 : (n = (string_length (input)))) (PreH10 : (valid_string input )) (PreH11 : (problem_91_pre_z input )) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH16 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH17 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= i)) ,
  (store_string S_pre input )
|--
  “ (n = (string_length (input))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_91_pre_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ ((sum + 1 ) = (bored_sum_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (isstart = (bored_isstart_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (0 <= (sum + 1 )) ” 
  &&  “ ((sum + 1 ) <= (i + 1 )) ”
  &&  (store_string S_pre input )
) \/
(
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) = 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 73)) (PreH7 : (isi = 1)) (PreH8 : ((Znth i (c_string (input)) 0) = 32)) (PreH9 : (i < n)) (PreH10 : (n = (string_length (input)))) (PreH11 : (valid_string input )) (PreH12 : (problem_91_pre_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH17 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH18 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH19 : (0 <= sum)) (PreH20 : (sum <= i)) ,
  TT && emp 
|--
  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ” 
  &&  “ (isstart = (bored_isstart_prefix_z ((i + 1 )) (input))) ” 
  &&  “ ((sum + 1 ) = (bored_sum_prefix_z ((i + 1 )) (input))) ”
  &&  emp
).

Definition is_bored_entail_wit_2_8_split_goal_1 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) = 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 73)) (PreH7 : (isi = 1)) (PreH8 : ((Znth i (c_string (input)) 0) = 32)) (PreH9 : (i < n)) (PreH10 : (n = (string_length (input)))) (PreH11 : (valid_string input )) (PreH12 : (problem_91_pre_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH17 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH18 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH19 : (0 <= sum)) (PreH20 : (sum <= i)) ,
  TT && emp 
|--
  “ (0 = (bored_isi_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_8_split_goal_2 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) = 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 73)) (PreH7 : (isi = 1)) (PreH8 : ((Znth i (c_string (input)) 0) = 32)) (PreH9 : (i < n)) (PreH10 : (n = (string_length (input)))) (PreH11 : (valid_string input )) (PreH12 : (problem_91_pre_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH17 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH18 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH19 : (0 <= sum)) (PreH20 : (sum <= i)) ,
  TT && emp 
|--
  “ (isstart = (bored_isstart_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_entail_wit_2_8_split_goal_3 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) <> 33)) (PreH3 : ((Znth i (c_string (input)) 0) <> 63)) (PreH4 : ((Znth i (c_string (input)) 0) <> 46)) (PreH5 : ((Znth i (c_string (input)) 0) = 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 73)) (PreH7 : (isi = 1)) (PreH8 : ((Znth i (c_string (input)) 0) = 32)) (PreH9 : (i < n)) (PreH10 : (n = (string_length (input)))) (PreH11 : (valid_string input )) (PreH12 : (problem_91_pre_z input )) (PreH13 : ((string_length (input)) < INT_MAX)) (PreH14 : (0 <= i)) (PreH15 : (i <= n)) (PreH16 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH17 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH18 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH19 : (0 <= sum)) (PreH20 : (sum <= i)) ,
  TT && emp 
|--
  “ ((sum + 1 ) = (bored_sum_prefix_z ((i + 1 )) (input))) ”
.

Definition is_bored_return_wit_1 := 
(
forall (S_pre: Z) (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (string_length (input)))) (PreH3 : (valid_string input )) (PreH4 : (problem_91_pre_z input )) (PreH5 : ((string_length (input)) < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH9 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH10 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH11 : (0 <= sum)) (PreH12 : (sum <= i)) ,
  (store_string S_pre input )
|--
  “ (problem_91_spec_z input sum ) ”
  &&  (store_string S_pre input )
) \/
(
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (valid_string input )) (PreH5 : (problem_91_pre_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH10 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH11 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH12 : (0 <= sum)) (PreH13 : (sum <= i)) ,
  TT && emp 
|--
  “ (problem_91_spec_z input sum ) ”
  &&  emp
).

Definition is_bored_return_wit_1_split_goal_1 := 
forall (input: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) (n: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (n = (string_length (input)))) (PreH4 : (valid_string input )) (PreH5 : (problem_91_pre_z input )) (PreH6 : ((string_length (input)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (sum = (bored_sum_prefix_z (i) (input)))) (PreH10 : (isstart = (bored_isstart_prefix_z (i) (input)))) (PreH11 : (isi = (bored_isi_prefix_z (i) (input)))) (PreH12 : (0 <= sum)) (PreH13 : (sum <= i)) ,
  TT && emp 
|--
  “ (problem_91_spec_z input sum ) ”
.

Definition is_bored_partial_solve_wit_1_pure := 
forall (S_pre: Z) (input: (@list Z)) (PreH1 : (valid_string input )) (PreH2 : (problem_91_pre_z input )) (PreH3 : ((string_length (input)) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  (store_string S_pre input )
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
.

Definition is_bored_partial_solve_wit_1_aux := 
forall (S_pre: Z) (input: (@list Z)) (PreH1 : (valid_string input )) (PreH2 : (problem_91_pre_z input )) (PreH3 : ((string_length (input)) < INT_MAX)) ,
  (store_string S_pre input )
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (problem_91_pre_z input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
  &&  (store_string S_pre input )
.

Definition is_bored_partial_solve_wit_1 := is_bored_partial_solve_wit_1_pure -> is_bored_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

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
Axiom proof_of_is_bored_partial_solve_wit_1_pure : is_bored_partial_solve_wit_1_pure.
Axiom proof_of_is_bored_partial_solve_wit_1 : is_bored_partial_solve_wit_1.

End VC_Correct.

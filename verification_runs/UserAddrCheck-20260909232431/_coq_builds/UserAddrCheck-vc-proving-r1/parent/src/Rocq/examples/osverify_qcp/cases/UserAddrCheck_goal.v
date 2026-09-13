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
Local Open Scope sac.

(*----- Function UserAddrCheck -----*)

Definition UserAddrCheck_safety_wit_1 := 
forall (addr_pre: Z) (a: Z) (PreH1 : (0 >= addr_pre)) (PreH2 : (addr_pre = a)) (PreH3 : (0 <= a)) (PreH4 : (a <= UINT_MAX)) ,
  ((( &( "addr" ) )) # UInt  |-> addr_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition UserAddrCheck_safety_wit_2 := 
forall (addr_pre: Z) (a: Z) (PreH1 : (addr_pre > 4294867295)) (PreH2 : (0 < addr_pre)) (PreH3 : (addr_pre = a)) (PreH4 : (0 <= a)) (PreH5 : (a <= UINT_MAX)) ,
  ((( &( "addr" ) )) # UInt  |-> addr_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition UserAddrCheck_safety_wit_3 := 
forall (addr_pre: Z) (a: Z) (PreH1 : (addr_pre <= 4294867295)) (PreH2 : (0 < addr_pre)) (PreH3 : (addr_pre = a)) (PreH4 : (0 <= a)) (PreH5 : (a <= UINT_MAX)) ,
  ((( &( "addr" ) )) # UInt  |-> addr_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition UserAddrCheck_return_wit_1 := 
forall (addr_pre: Z) (a: Z) (PreH1 : (addr_pre <= 4294867295)) (PreH2 : (0 < addr_pre)) (PreH3 : (addr_pre = a)) (PreH4 : (0 <= a)) (PreH5 : (a <= UINT_MAX)) ,
  TT && emp 
|--
  “ (0 < a) ” 
  &&  “ (a <= 4294867295) ” 
  &&  “ (1 = 1) ”
  &&  emp
.

Definition UserAddrCheck_return_wit_2 := 
forall (addr_pre: Z) (a: Z) (PreH1 : (0 >= addr_pre)) (PreH2 : (addr_pre = a)) (PreH3 : (0 <= a)) (PreH4 : (a <= UINT_MAX)) ,
  TT && emp 
|--
  “ (a <= 0) ” 
  &&  “ (0 = 0) ”
  &&  emp
.

Definition UserAddrCheck_return_wit_3 := 
forall (addr_pre: Z) (a: Z) (PreH1 : (addr_pre > 4294867295)) (PreH2 : (0 < addr_pre)) (PreH3 : (addr_pre = a)) (PreH4 : (0 <= a)) (PreH5 : (a <= UINT_MAX)) ,
  TT && emp 
|--
  “ (4294867295 < a) ” 
  &&  “ (0 = 0) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_UserAddrCheck_safety_wit_1 : UserAddrCheck_safety_wit_1.
Axiom proof_of_UserAddrCheck_safety_wit_2 : UserAddrCheck_safety_wit_2.
Axiom proof_of_UserAddrCheck_safety_wit_3 : UserAddrCheck_safety_wit_3.
Axiom proof_of_UserAddrCheck_return_wit_1 : UserAddrCheck_return_wit_1.
Axiom proof_of_UserAddrCheck_return_wit_2 : UserAddrCheck_return_wit_2.
Axiom proof_of_UserAddrCheck_return_wit_3 : UserAddrCheck_return_wit_3.

End VC_Correct.

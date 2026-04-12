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
Require Import SimpleC.EE.Applications.LiteOS.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications.LiteOS.lib.Los_Verify_State_def.
Require Import SimpleC.EE.Applications.LiteOS.lib.sortlink.
Require Import SimpleC.EE.Applications.LiteOS.lib.dll.
Require Import SimpleC.EE.Applications.LiteOS.lib.tick_backup.
Local Open Scope sac.
From SimpleC.EE.QCP_democases Require Import common_strategy_goal.
From SimpleC.EE.QCP_democases Require Import common_strategy_proof.
From SimpleC.EE.Applications Require Import los_sortlink_strategy_goal.
From SimpleC.EE.Applications Require Import los_sortlink_strategy_proof.

(*----- Function GetSortLinkNextExpireTime -----*)

Definition GetSortLinkNextExpireTime_safety_wit_1 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (retval: Z) ,
  [| ((map (sortedLinkNodeMapping) (l)) = nil) |] 
  &&  [| (retval = 1) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval = 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "sortHead" ) )) # Ptr  |-> sortHead_pre)
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "head" ) )) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "tickPrecision" ) )) # UInt64  |-> tickPrecision_pre)
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  [| False |]
.

Definition GetSortLinkNextExpireTime_safety_wit_2 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) ,
  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "sortHead" ) )) # Ptr  |-> sortHead_pre)
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "head" ) )) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "tickPrecision" ) )) # UInt64  |-> tickPrecision_pre)
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  [| False |]
.

Definition GetSortLinkNextExpireTime_entail_wit_1 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (pt: Z) (h: Z) ,
  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  ((( &( "list" ) )) # Ptr  |-> h)
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  [| ((obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_entail_wit_2_1 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) ,
  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval = 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval = 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_entail_wit_2_2 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (retval_2: Z) ,
  [| ((map (sortedLinkNodeMapping) (l)) = nil) |] 
  &&  [| (retval_2 = 1) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval_2 = 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  EX (a: (@DL_Node (@sortedLinkNode A)))  (l1: (@list (@DL_Node (@sortedLinkNode A))))  (retval: Z) ,
  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval = 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_entail_wit_3_1 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) ,
  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  EX (retval: Z) ,
  [| ((map (sortedLinkNodeMapping) (l)) = nil) |] 
  &&  [| (retval = 1) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_entail_wit_3_2 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (retval: Z) ,
  [| ((map (sortedLinkNodeMapping) (l)) = nil) |] 
  &&  [| (retval = 1) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  [| ((map (sortedLinkNodeMapping) (l)) = nil) |] 
  &&  [| (retval = 1) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_return_wit_1 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (retval: Z) ,
  [| ((map (sortedLinkNodeMapping) (l)) = nil) |] 
  &&  [| (retval = 1) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval <> 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  [| ((unsigned_last_nbits ((((2^64) - 1 ) - tickPrecision_pre )) (64)) = (getFirstNodeExpireTime (l) (startTime_pre) (tickPrecision_pre))) |]
  &&  (store_sorted_dll storeA &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_return_wit_2 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (pt: Z) (pl: Z) ,
  [| ((responseTime ((data (a)))) <= (unsigned_last_nbits ((startTime_pre + tickPrecision_pre )) (64))) |] 
  &&  [| (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval = 0) |]
  &&  (storeA &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") (sl_data ((data (a)))) )
  **  ((&((retval_2)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (responseTime ((data (a)))))
  **  ((&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> pl)
  **  ((&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) pl &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt l1 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  [| ((unsigned_last_nbits ((startTime_pre + tickPrecision_pre )) (64)) = (getFirstNodeExpireTime (l) (startTime_pre) (tickPrecision_pre))) |]
  &&  (store_sorted_dll storeA &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_return_wit_3 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (pt: Z) (pl: Z) ,
  [| ((responseTime ((data (a)))) > (unsigned_last_nbits ((startTime_pre + tickPrecision_pre )) (64))) |] 
  &&  [| (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval = 0) |]
  &&  (storeA &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") (sl_data ((data (a)))) )
  **  ((&((retval_2)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (responseTime ((data (a)))))
  **  ((&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> pl)
  **  ((&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) pl &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt l1 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  [| ((responseTime ((data (a)))) = (getFirstNodeExpireTime (l) (startTime_pre) (tickPrecision_pre))) |]
  &&  (store_sorted_dll storeA &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_partial_solve_wit_1 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) ,
  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_sorted_dll storeA &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_sorted_dll storeA &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_partial_solve_wit_2 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (pt: Z) (h: Z) ,
  [| ((obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_partial_solve_wit_3 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) ,
  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_partial_solve_wit_4 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) ,
  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval = 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval = 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_partial_solve_wit_5_pure := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval: Z) ,
  [| (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval_2 = 0) |]
  &&  ((( &( "listSorted" ) )) # Ptr  |-> retval)
  **  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "sortHead" ) )) # Ptr  |-> sortHead_pre)
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "head" ) )) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "tickPrecision" ) )) # UInt64  |-> tickPrecision_pre)
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  [| (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (ptr (a))) |]
.

Definition GetSortLinkNextExpireTime_partial_solve_wit_5_aux := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval: Z) ,
  [| (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval_2 = 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  [| (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (ptr (a))) |] 
  &&  [| (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval_2 = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval_2 = 0) |]
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons ((Build_DL_Node ((mksortedLinkNode ((sl_data ((data (a))))) ((responseTime ((data (a))))))) (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode")))) (l1)) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_partial_solve_wit_5 := GetSortLinkNextExpireTime_partial_solve_wit_5_pure -> GetSortLinkNextExpireTime_partial_solve_wit_5_aux.

Definition GetSortLinkNextExpireTime_partial_solve_wit_6 := 
forall (A: Type) (tickPrecision_pre: Z) (startTime_pre: Z) (sortHead_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (pt: Z) (pl: Z) ,
  [| (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval = 0) |]
  &&  ((&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> pl)
  **  ((&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) pl &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt l1 )
  **  (storesortedLinkNode storeA &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode ((sl_data ((data (a))))) ((responseTime ((data (a)))))) )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
|--
  [| (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) |] 
  &&  [| (increasingSortedNode l ) |] 
  &&  [| ((startTime_pre + tickPrecision_pre ) <= ULLONG_MAX) |] 
  &&  [| (startTime_pre >= 0) |] 
  &&  [| (startTime_pre <= ULLONG_MAX) |] 
  &&  [| (tickPrecision_pre >= 0) |] 
  &&  [| (tickPrecision_pre <= ULLONG_MAX) |] 
  &&  [| (retval = 0) |]
  &&  (storesortedLinkNode storeA &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode ((sl_data ((data (a))))) ((responseTime ((data (a)))))) )
  **  ((&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> pl)
  **  ((&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) pl &((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt l1 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((2^64) - 1 ))
.

Definition GetSortLinkNextExpireTime_which_implies_wit_1 := 
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortHead: Z) ,
  (store_sorted_dll storeA &((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink") l )
|--
  EX (pt: Z)  (h: Z) ,
  [| (increasingSortedNode l ) |]
  &&  ((&((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
.

Definition GetSortLinkNextExpireTime_which_implies_wit_2 := 
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (pt: Z) (h: Z) (sortHead: Z) ,
  ((&((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
|--
  (store_dll (storesortedLinkNode (storeA)) &((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
.

Definition GetSortLinkNextExpireTime_which_implies_wit_3 := 
forall (A: Type) (storeA: (Z -> (A -> Assertion))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (t: Z) (al: A) (listSorted: Z) (sortHead: Z) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink") (cons ((Build_DL_Node ((mksortedLinkNode (al) (t))) (&((listSorted)  # "SortLinkList" ->ₛ "sortLinkNode")))) (l1)) )
|--
  EX (pt: Z)  (pl: Z) ,
  ((&((listSorted)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> pl)
  **  ((&((listSorted)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> &((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((&((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> &((listSorted)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) pl &((listSorted)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortHead)  # "SortLinkAttribute" ->ₛ "sortLink") pt l1 )
  **  (storesortedLinkNode storeA &((listSorted)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (al) (t)) )
.

Definition GetSortLinkNextExpireTime_which_implies_wit_4 := 
forall (A: Type) (storeA: (Z -> (A -> Assertion))) (t: Z) (al: A) (listSorted: Z) ,
  (storesortedLinkNode storeA &((listSorted)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (al) (t)) )
|--
  (storeA &((listSorted)  # "SortLinkList" ->ₛ "sortLinkNode") al )
  **  ((&((listSorted)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
.

Definition LOS_ListEmpty_derive_getfirstSpec_by_highSpec := 
forall (A: Type) ,
forall (node_pre: Z) (l_getfirstSpec: (@list (@DL_Node A))) (storeA_getfirstSpec: (Z -> (A -> Assertion))) ,
  (store_dll storeA_getfirstSpec node_pre l_getfirstSpec )
|--
EX (A: Type) ,
EX (storeA_highSpec: (Z -> (A -> Assertion))) (l_highSpec: (@list (@DL_Node A))) ,
  ((store_dll storeA_highSpec node_pre l_highSpec ))
  **
  (((EX retval_2,
  [| (l_highSpec = nil) |] 
  &&  [| (retval_2 = 1) |]
  &&  (store_dll storeA_highSpec node_pre l_highSpec ))
  ||
  (EX retval_2,
  [| (l_highSpec <> nil) |] 
  &&  [| (retval_2 = 0) |]
  &&  (store_dll storeA_highSpec node_pre l_highSpec )))
  -*
  ((EX a l1 retval,
  [| (l_getfirstSpec <> nil) |] 
  &&  [| (retval = 0) |] 
  &&  [| (l_getfirstSpec = (cons (a) (l1))) |]
  &&  (store_dll storeA_getfirstSpec node_pre (cons (a) (l1)) ))
  ||
  (EX retval,
  [| (l_getfirstSpec = nil) |] 
  &&  [| (retval = 1) |]
  &&  (store_dll storeA_getfirstSpec node_pre l_getfirstSpec ))))
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include los_sortlink_Strategy_Correct.

Axiom proof_of_GetSortLinkNextExpireTime_safety_wit_1 : GetSortLinkNextExpireTime_safety_wit_1.
Axiom proof_of_GetSortLinkNextExpireTime_safety_wit_2 : GetSortLinkNextExpireTime_safety_wit_2.
Axiom proof_of_GetSortLinkNextExpireTime_entail_wit_1 : GetSortLinkNextExpireTime_entail_wit_1.
Axiom proof_of_GetSortLinkNextExpireTime_entail_wit_2_1 : GetSortLinkNextExpireTime_entail_wit_2_1.
Axiom proof_of_GetSortLinkNextExpireTime_entail_wit_2_2 : GetSortLinkNextExpireTime_entail_wit_2_2.
Axiom proof_of_GetSortLinkNextExpireTime_entail_wit_3_1 : GetSortLinkNextExpireTime_entail_wit_3_1.
Axiom proof_of_GetSortLinkNextExpireTime_entail_wit_3_2 : GetSortLinkNextExpireTime_entail_wit_3_2.
Axiom proof_of_GetSortLinkNextExpireTime_return_wit_1 : GetSortLinkNextExpireTime_return_wit_1.
Axiom proof_of_GetSortLinkNextExpireTime_return_wit_2 : GetSortLinkNextExpireTime_return_wit_2.
Axiom proof_of_GetSortLinkNextExpireTime_return_wit_3 : GetSortLinkNextExpireTime_return_wit_3.
Axiom proof_of_GetSortLinkNextExpireTime_partial_solve_wit_1 : GetSortLinkNextExpireTime_partial_solve_wit_1.
Axiom proof_of_GetSortLinkNextExpireTime_partial_solve_wit_2 : GetSortLinkNextExpireTime_partial_solve_wit_2.
Axiom proof_of_GetSortLinkNextExpireTime_partial_solve_wit_3 : GetSortLinkNextExpireTime_partial_solve_wit_3.
Axiom proof_of_GetSortLinkNextExpireTime_partial_solve_wit_4 : GetSortLinkNextExpireTime_partial_solve_wit_4.
Axiom proof_of_GetSortLinkNextExpireTime_partial_solve_wit_5_pure : GetSortLinkNextExpireTime_partial_solve_wit_5_pure.
Axiom proof_of_GetSortLinkNextExpireTime_partial_solve_wit_5 : GetSortLinkNextExpireTime_partial_solve_wit_5.
Axiom proof_of_GetSortLinkNextExpireTime_partial_solve_wit_6 : GetSortLinkNextExpireTime_partial_solve_wit_6.
Axiom proof_of_GetSortLinkNextExpireTime_which_implies_wit_1 : GetSortLinkNextExpireTime_which_implies_wit_1.
Axiom proof_of_GetSortLinkNextExpireTime_which_implies_wit_2 : GetSortLinkNextExpireTime_which_implies_wit_2.
Axiom proof_of_GetSortLinkNextExpireTime_which_implies_wit_3 : GetSortLinkNextExpireTime_which_implies_wit_3.
Axiom proof_of_GetSortLinkNextExpireTime_which_implies_wit_4 : GetSortLinkNextExpireTime_which_implies_wit_4.
Axiom proof_of_LOS_ListEmpty_derive_getfirstSpec_by_highSpec : LOS_ListEmpty_derive_getfirstSpec_by_highSpec.

End VC_Correct.

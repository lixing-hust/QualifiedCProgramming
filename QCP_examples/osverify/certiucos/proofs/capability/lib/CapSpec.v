Require Import include_frm.
Require Import Lists.ListSet.
Require Import os_code_defs.
Require Import os_ucos_h.

Require Import os_inv.
Require Import abs_op.
Require Import abs_op_capability.
Require Import int_lock.
Require Import os_core.
Require Import ios_cap_defs.
Require Import code_notations.
Require Import ACSpace_defs.
Require Import ifun_spec.
Require Import CapPure.
Require Import Classical.
Require Import ucos_frmaop.


Open Scope Z_scope.
Open Scope int_scope.
Open Scope code_scope.
Require Import List.
Set Nested Proofs Allowed.


(*GetObjSlot*)

Local Ltac GoodFunAsrt_solver ::=
  repeat
   (split; try apply GoodFunAsrt_Aarray;
     try apply GoodFunAsrt_Astruct;
     try apply GoodFunAsrt_AEventData;
     try apply GoodFunAsrt_evsllseg;
     try apply GoodFunAsrt_tcbdllseg; try apply GoodFunAsrt_dllseg;
     try apply GoodFunAsrt_ecbf_sll; try apply GoodFunAsrt_sll;
     try apply GoodFunAsrt_qblkf_sll;
     try apply GoodFunAsrt_invlth_isr';
     try apply GoodFunAsrt_tcbdllflag;
     try apply GoodFunAsrt_sllfreeflag;
     try apply GoodFunAsrt_Aarray_new; 
     try apply GoodFunAsrt_pos_sllseg; 
     try apply GoodFunAsrt_err_sllseg; 
     try apply GoodFunAsrt_AEvAtomHeap; 
     try apply GoodFunAsrt_AEvStructHeap; 
     try apply GoodFunAsrt_AEvArrayHeap; 
     try apply GoodFunAsrt_llsegevaux; 
     try apply GoodFunAsrt_AOScoreheape;
     try apply GoodFunAsrt_AOScoreheapl;
     try apply GoodFunAsrt_AOScoreheapt;
     try apply GoodFunAsrt_AOSIPCMem_aux;
     try apply GoodFunAsrt_Adynheap;
     try (simple apply GoodFunAsrt_AOSCSpacePrioTbl);
     auto).



Definition Get_Obj_SlotPre'(vl:vallist) (logicl:list logicvar) ct:=
  EX prio func_object er s cs isr b i pointervl ptrvl priovl cspacels ,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  AOSCSpacePrioTbl  (b, i) ptrvl priovl cspacels ** 
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] **
  AOSCSpaceObjectPointer pointervl ** 
  [| nth_val 0 vl = Some (Vint32 prio) |] **
  [| nth_val 1 vl = Some func_object |] **
  [|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er)::(logic_lv ptrvl) :: (logic_cspacel priovl) :: (logic_lv pointervl) ::
  (logic_code s) :: (logic_abscap cspacels) :: (logic_val (Vptr(b, i))) ::nil|] **
  [|isptr func_object|] **
  p_local OSLInv ct init_lg.

Theorem Get_Obj_SlotPreGood (vl:vallist) ll ct:
  GoodFunAsrt (Get_Obj_SlotPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition Get_Obj_SlotPre : fpre :=
  fun vl ll ct => mkfunasrt (Get_Obj_SlotPreGood vl ll ct).

Definition get_slots prio vl :=
  match nth_cspace prio vl with
  | Some (cnode, _, _, _, _) =>
    match cnode with 
    |(_, _, slotvl) =>
      Some slotvl
    end 
  | _ => None
end.

Definition Slots_neq_object vl object:=
  forall idx a b c d e f, 
  0<= idx < Z.of_nat(length vl) ->
  nth_slots (Z.to_nat idx) vl = Some(a, (b, c)) ->
  c = ((d, e), f) ->
  ~(f = object).

Definition Slots_eq_object idx vl object:=
  exists a b c d e f, 
  0<= idx < Z.of_nat(length vl) /\
  nth_slots (Z.to_nat idx) vl = Some(a, (b, c)) /\
  c = ((d, e), f) /\
  (f = object).

Definition Get_Obj_SlotPost'(vl:vallist) (v: option val) (logicl:list logicvar) ct:=
  EX prio func_object er s cs isr b i pointervl ptrvl priovl cspacels,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  [| nth_val 0 vl = Some (Vint32 prio) |] **
  [| nth_val 1 vl = Some func_object |] **
  AOSCSpacePrioTbl  (b, i) ptrvl priovl cspacels ** 
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] **
  AOSCSpaceObjectPointer pointervl**
  [|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er)::(logic_lv ptrvl):: (logic_cspacel priovl) :: (logic_lv pointervl) :: 
  (logic_code s) :: (logic_abscap cspacels):: (logic_val (Vptr(b, i))) ::nil|] **
  [|isptr func_object|] **
  p_local OSLInv ct init_lg **(
  ([|(Int.unsigned prio) < OS_LOWEST_PRIO |] **( 
        ([|nth_val' (Z.to_nat(Int.unsigned prio)) ptrvl = Vnull|] ** [|v = Some(Vint32(Int.repr SLOT_NULL_CAP))|])\\//
        ([|nth_val' (Z.to_nat(Int.unsigned prio)) ptrvl <> Vnull|] ** 
        (EX endPtr, 
        [|nth_val' (Z.to_nat(Int.unsigned prio)) pointervl = (Vint32 endPtr)|] **
            (   
              ( 
                EX i0 vll11 vll12 vll2,
                [|get_slots (Z.to_nat(Int.unsigned prio)) priovl = Some (vll11++vll12++vll2)|] **
                [|length vll11 = Z.to_nat(OBJ_POSITION)|] **
                [|length (vll11++vll12) = Z.to_nat(Int.unsigned endPtr)|] **
                [|Slots_eq_object i0 vll12 func_object|] ** 
                [|v = Some(Vint32 (Int.repr (i0 + OBJ_POSITION))) /\OBJ_POSITION <= (i0 + OBJ_POSITION) < 255|] (*while中的if成立*)
              )\\//
              (
                EX vll11 vll12 vll2,
                [|get_slots (Z.to_nat(Int.unsigned prio)) priovl = Some (vll11++vll12++vll2)|] **
                [|length vll11 = Z.to_nat(OBJ_POSITION)|] **
                [|length (vll11++vll12) = Z.to_nat(Int.unsigned endPtr)|] **
                [|Slots_neq_object vll12 func_object|] ** 
                [|v = Some(Vint32 (Int.repr SLOT_NULL_CAP))|]  
                (*while中的if不成立或者不进入循环*)
              )
            )))
        )
    ) 
  
      \\// ([|(Int.unsigned prio) >= OS_LOWEST_PRIO|]
            ** [|v = Some (Vint32 (Int.repr OS_PRIO_INVALID))|]
            (*第一个if成立*))).

Theorem Get_Obj_SlotPostGood (vl:vallist) v ll ct:
  GoodFunAsrt (Get_Obj_SlotPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition Get_Obj_SlotPost : fpost :=
  fun vl v ll ct => mkfunasrt (Get_Obj_SlotPostGood vl v ll ct).
Definition Get_Obj_Slot_spec : fspec:= (Get_Obj_SlotPre,Get_Obj_SlotPost,(Int32u, Tint8::(Tptr Tvoid)::nil)).

(*ucosGrantCap*)

Definition cspacelist_inj (v : option (list cspace_val_type)) :=
  match v with
    | Some v' => v'
    | None => nil
  end.

Definition ucos_Grant_CapPre' (vl:vallist) (logicl:list logicvar) ct:=
  EX destTask_Prio cap_Class cap_Right er s cs isr ptrvl priotbl b i  cspacels,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  [| nth_val 0 vl = Some (Vint32 destTask_Prio) |] **
  [| nth_val 1 vl = Some (Vint32 cap_Class) |] **
  [| nth_val 2 vl = Some (Vint32 cap_Right) |] **
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
  AOSCSpacePrioTbl (b, i) ptrvl priotbl cspacels** 
  [|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er)::(logic_cspacel priotbl) :: (logic_code s) :: (logic_abscap cspacels)::
  (logic_lv ptrvl)::nil|] **
  p_local OSLInv ct init_lg.
Theorem ucos_Grant_CapPreGood (vl:vallist) ll ct:
  GoodFunAsrt (ucos_Grant_CapPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition ucos_Grant_CapPre : fpre :=
  fun vl ll ct => mkfunasrt (ucos_Grant_CapPreGood vl ll ct).

Definition ucos_Grant_CapPost'(vl:vallist) (v: option val) (logicl:list logicvar) ct:=
  EX destTask_Prio cap_Class cap_Right er s cs isr ptrvl priotbl priotbl'
  b i cspacels x y origin_capRight z,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  [| nth_val 0 vl = Some (Vint32 destTask_Prio) |] **
  [| nth_val 1 vl = Some (Vint32 cap_Class) |] **
  [| nth_val 2 vl = Some (Vint32 cap_Right) |] **
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
  AOSCSpacePrioTbl (b, i) ptrvl priotbl' cspacels** 
  [|logicl = (logic_cs cs) :: (logic_isr isr) :: (logic_ier er):: (logic_cspacel priotbl) :: (logic_code s) ::(logic_abscap cspacels)::(logic_lv ptrvl)::nil|] **
  p_local OSLInv ct init_lg **
  (
  ([|(CAP_NULL_CLASS > Int.unsigned cap_Class \/ Int.unsigned cap_Class > CAP_CHANNEL_CLASS)
  \/(Int.unsigned destTask_Prio >= 64 \/ (nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl = Vnull))|] **(
   [|v = Some(Vint32(Int.repr CNODE_GRANT_FAILURE))|]**[|priotbl'= priotbl|]) \\//
   ( [|(CAP_NULL_CLASS <= Int.unsigned cap_Class <= CAP_CHANNEL_CLASS)
   /\(Int.unsigned destTask_Prio< 64) /\ (nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl <> Vnull)|] **
    ([|v = Some(Vint32 (Int.repr 0))|] ** [|get_capability (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat(Int.unsigned cap_Class)) priotbl = Some (x, (y, origin_capRight, z))|] **
    [|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat(Int.unsigned cap_Class)) priotbl
    (((Int.repr CAP_CATEGORY_TYPE), (cap_Class, Int.or(Int.and origin_capRight (Int.repr 4095)) cap_Right, z))))|]))
  )).

Theorem ucos_Grant_CapPostGood (vl:vallist) v ll ct:
  GoodFunAsrt (ucos_Grant_CapPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition ucos_Grant_CapPost : fpost :=
  fun vl v ll ct => mkfunasrt (ucos_Grant_CapPostGood vl v  ll ct).

Definition ucos_Grant_Cap_spec : fspec :=
  (ucos_Grant_CapPre,ucos_Grant_CapPost,(Int8u, Tint8::Tint32::Tint32::nil)).


(*ucosCNodeMint*)
Definition ucos_CNode_MintPre'(vl:vallist) (logicl:list logicvar) ct:=
  EX destTask_Prio srcTask_Prio func_capability rights  er s b i cs isr
  ptrvl priotbl cspacels,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  [| nth_val 0 vl = Some (Vint32 destTask_Prio) |] **
  [| nth_val 1 vl = Some (Vint32 srcTask_Prio) |] **
  [| nth_val 2 vl = Some (Vint32 func_capability) |] **
  [| nth_val 3 vl = Some (Vint32 rights)|] **  
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
  AOSCSpacePrioTbl (b, i) ptrvl priotbl cspacels ** 
  [|logicl=(logic_cs cs)::(logic_isr isr)::(logic_ier er)::(logic_cspacel priotbl)::(logic_code s)::(logic_abscap cspacels)::(logic_lv ptrvl)::nil|] **  (*之所以写在这里就是要获取pCSpace2之前的值，因为pCspace1可能与pCspace2相同*)
  p_local OSLInv ct init_lg.

Theorem ucos_CNode_MintPreGood (vl:vallist) ll ct:
  GoodFunAsrt (ucos_CNode_MintPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition ucos_CNode_MintPre : fpre :=
  fun vl ll ct => mkfunasrt (ucos_CNode_MintPreGood vl ll ct).

Definition ucos_CNode_MintPost'(vl:vallist) (v: option val)(logicl:list logicvar) ct:=
  EX destTask_Prio srcTask_Prio func_capability rights  er s b i cs isr
  ptrvl priotbl priotbl' cspacels captype_val categorycontent_val categoryright_val z 
  captype_val_dest categorycontent_val_dest categoryright_val_dest z_dest,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  [| nth_val 0 vl = Some (Vint32 destTask_Prio) |] **
  [| nth_val 1 vl = Some (Vint32 srcTask_Prio) |] **
  [| nth_val 2 vl = Some (Vint32 func_capability) |] **
  [| nth_val 3 vl = Some (Vint32 rights)|] **  
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
  AOSCSpacePrioTbl (b, i) ptrvl priotbl' cspacels**
  [|logicl=(logic_cs cs)::(logic_isr isr)::(logic_ier er)::(logic_cspacel priotbl)::(logic_code s)::(logic_abscap cspacels)::(logic_lv ptrvl)::nil|] **
   p_local OSLInv ct init_lg **([|
  (CAP_NULL_CLASS > Int.unsigned func_capability \/ Int.unsigned func_capability > CAP_CHANNEL_CLASS)
  \/(Int.unsigned destTask_Prio >= 64 \/ Int.unsigned srcTask_Prio >= 64) \/(nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl = Vnull \/ nth_val' (Z.to_nat(Int.unsigned srcTask_Prio)) ptrvl = Vnull)
  |] ** [|v = Some (Vint32 ($ CNODE_MINT_FAILURE ))|] ** [|priotbl' = priotbl|]\\//(
  [|(CAP_NULL_CLASS <=Int.unsigned func_capability <= CAP_CHANNEL_CLASS)
  /\(Int.unsigned destTask_Prio < 64 /\ Int.unsigned srcTask_Prio < 64) /\(nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl <> Vnull /\ nth_val' (Z.to_nat(Int.unsigned srcTask_Prio)) ptrvl <> Vnull)|] **
  ([|get_capability (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) 
  priotbl = Some(captype_val, (categorycontent_val, categoryright_val, z))|] **
  [|get_capability (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) 
  priotbl = Some(captype_val_dest, (categorycontent_val_dest, categoryright_val_dest, z_dest))|] ** 
  ([|(captype_val <> ($ CAP_CATEGORY_TYPE)\/ Int.and (Int.not categoryright_val) rights <> $0
  \/ categoryright_val = rights)|]** [|v = Some (Vint32 ($ CNODE_MINT_FAILURE ))|] ** [|priotbl' = priotbl|]\\//(
    [|captype_val = ($ CAP_CATEGORY_TYPE) /\ Int.and (Int.not categoryright_val) rights = $0
    /\ categoryright_val <> rights|] ** 
    [|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl
    ($CAP_CATEGORY_TYPE , (categorycontent_val, rights, z_dest)))|] **
    [|v = Some (Vint32 ($ CNODE_NONE_FAULT))|]))
  ))).

Theorem ucos_CNode_MintPostGood (vl:vallist)(v:option val) ll ct:
  GoodFunAsrt (ucos_CNode_MintPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition ucos_CNode_MintPost : fpost :=
  fun vl v ll ct => mkfunasrt (ucos_CNode_MintPostGood vl v ll ct).
Definition ucos_CNode_Mint_spec : fspec:= (ucos_CNode_MintPre,ucos_CNode_MintPost,(Int8u, Tint8::Tint8::Tint32::Tint32::nil)).


(*ucos_CNode_Copy*)
Definition ucos_CNode_CopyPre'(vl:vallist) (logicl:list logicvar) ct:=
  EX destTask_Prio srcTask_Prio func_capability  er s b i cs isr
  ptrvl priotbl cspacels pointervl,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  [| nth_val 0 vl = Some (Vint32 destTask_Prio) |] **
  [| nth_val 1 vl = Some (Vint32 srcTask_Prio) |] **
  [| nth_val 2 vl = Some (Vint32 func_capability) |] **
  AOSCSpaceObjectPointer pointervl ** 
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
  [|Int.unsigned destTask_Prio > Int.unsigned srcTask_Prio|] ** 
  AOSCSpacePrioTbl (b, i) ptrvl priotbl cspacels** 
  (*[|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er) ::
  (logic_cspacel priotbl) :: (logic_lv pointervl) :: (logic_code s) ::(logic_abscap cspacels)::nil|] ** *)
  [|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er) ::
  (logic_cspacel priotbl) :: (logic_lv pointervl) ::(logic_code s)::(logic_abscap cspacels)::(logic_lv ptrvl)::nil|] **
  p_local OSLInv ct init_lg ** 
  [|Int.unsigned destTask_Prio < OS_LOWEST_PRIO|] **
  [|Int.unsigned srcTask_Prio < OS_LOWEST_PRIO|] **
  [|Int.unsigned func_capability < SLOT_NUM|].
  (*这里是由调用copy函数的得到的*)

Theorem ucos_CNode_CopyPreGood (vl:vallist) ll ct:
  GoodFunAsrt (ucos_CNode_CopyPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition ucos_CNode_CopyPre : fpre :=
  fun vl ll ct => mkfunasrt (ucos_CNode_CopyPreGood vl ll ct).


Definition GetObjSlotRetval prio ptrvl pointervl priovl func_object v:=
  (
  ([|(Int.unsigned prio) < OS_LOWEST_PRIO |] **( 
        ([|nth_val' (Z.to_nat(Int.unsigned prio)) ptrvl = Vnull|] ** [|v = Some(Vint32(Int.repr SLOT_NULL_CAP))|])\\//
        ([|nth_val' (Z.to_nat(Int.unsigned prio)) ptrvl <> Vnull|] ** 
        (EX endPtr, 
        [|nth_val' (Z.to_nat(Int.unsigned prio)) pointervl = (Vint32 endPtr)|] **
            (   
              ( 
                EX i0 vll11 vll12 vll2,
                [|get_slots (Z.to_nat(Int.unsigned prio)) priovl = Some (vll11++vll12++vll2)|] **
                [|length vll11 = Z.to_nat(OBJ_POSITION)|] **
                [|length (vll11++vll12) = Z.to_nat(Int.unsigned endPtr)|] **
                [|Slots_eq_object i0 vll12 func_object|] ** 
                [|v = Some(Vint32 (Int.repr (i0 + OBJ_POSITION))) /\OBJ_POSITION <= (i0 + OBJ_POSITION) < 255|] (*while中的if成立*)
              )\\//
              (
                EX vll11 vll12 vll2,
                [|get_slots (Z.to_nat(Int.unsigned prio)) priovl = Some (vll11++vll12++vll2)|] **
                [|length vll11 = Z.to_nat(OBJ_POSITION)|] **
                [|length (vll11++vll12) = Z.to_nat(Int.unsigned endPtr)|] **
                [|Slots_neq_object vll12 func_object|] ** 
                [|v = Some(Vint32 (Int.repr SLOT_NULL_CAP))|]  
                (*while中的if不成立或者不进入循环*)
              )
            )))
        )
    )\\// ([|(Int.unsigned prio) >= OS_LOWEST_PRIO|]
            ** [|v = Some (Vint32 (Int.repr OS_PRIO_INVALID))|]
            (*第一个if成立*))).

Definition Vint32_inj (v : val) :=
  match v with
    | Vint32 v' => v'
    | _ => $0
  end.

(*Definition ucos_CNode_CopyPost'(vl:vallist) (v: option val)(logicl:list logicvar) ct:=
  (*EX destTask_Prio srcTask_Prio func_capability er s b i cs isr
  ptrvl priotbl  priotbl' cspacels pointervl pointervl'  captype_val categorycontent_val categoryright_val 
  categoryobject_val  origin_right origin_object,*)
  EX destTask_Prio srcTask_Prio func_capability er s b i cs isr
  ptrvl priotbl  priotbl'  priotbl'' priotbl''' cspacels pointervl pointervl' captype_val categorycontent_val categoryright_val 
  categoryobject_val  origin_right origin_object captype_val_dest categorycontent_val_dest categoryright_val_dest,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  [| nth_val 0 vl = Some (Vint32 destTask_Prio) |] **
  [| nth_val 1 vl = Some (Vint32 srcTask_Prio) |] **
  [| nth_val 2 vl = Some (Vint32 func_capability) |] **
  AOSCSpaceObjectPointer pointervl' ** 
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
  AOSCSpacePrioTbl (b, i) ptrvl priotbl''' cspacels ** 
  (*[|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er)::
  (logic_cspacel priotbl) :: (logic_lv pointervl)::(logic_code s) ::(logic_abscap cspacels)::nil|] ** *)
  [|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er)::
  (logic_cspacel priotbl) :: (logic_lv pointervl)::(logic_code s)::(logic_abscap cspacels)::(logic_lv ptrvl)::nil|] **
  p_local OSLInv ct init_lg ** 
  (
    [|nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl = Vnull \/
    nth_val' (Z.to_nat(Int.unsigned srcTask_Prio)) ptrvl = Vnull|] ** [|v = Some(Vint32(Int.repr CNODE_COPY_FAILURE)) /\ priotbl''' = priotbl /\ pointervl' = pointervl|] \\//
    ([|nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl <> Vnull /\
    nth_val' (Z.to_nat(Int.unsigned srcTask_Prio)) ptrvl <> Vnull|] **
    [|get_capability (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) 
    priotbl = Some(captype_val, (categorycontent_val, categoryright_val, categoryobject_val))|] **
    [|get_capability (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) 
    priotbl = Some(captype_val_dest, (categorycontent_val_dest, categoryright_val_dest, origin_object))|] **
    (
    ([|(Int.unsigned captype_val <> CAP_CATEGORY_TYPE) /\ (Int.unsigned captype_val <> CAP_OBJECT_TYPE)|]
    ** [|v = Some(Vint32 ($CNODE_COPY_FAILURE))|]
    (* ** [|priotbl' = priotbl /\ pointervl' = pointervl|]) \\//( *)
    ** [|priotbl''' = priotbl /\ pointervl' = pointervl|]) \\//(
    [|(Int.unsigned captype_val = CAP_CATEGORY_TYPE)|] **
    [|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl
    ($CAP_CATEGORY_TYPE , (categorycontent_val, categoryright_val, origin_object)))|] ** 
    [|priotbl'' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl'
    ($0 , ($0, $0, categoryobject_val)))|] **
    [|priotbl''' = (update_nth_cspace_slots_type (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl''
    ($ SLOT_NULL_CAP))|] **
    [|pointervl' = pointervl|] ** [|v = Some(Vint32 ($CNODE_NONE_FAULT))|]
    ) \\// ([|(Int.unsigned captype_val = CAP_OBJECT_TYPE)|] **
      (EX idxval idxz,
      GetObjSlotRetval destTask_Prio ptrvl pointervl priotbl categoryobject_val idxval **
        (*[|(Vint32 (Int.repr idxz)) = (val_inj idxval)|] **( *)
        [| idxz = Int.unsigned (Vint32_inj(val_inj idxval))|] **(
       [|idxz = SLOT_NULL_CAP|] ** (
        EX pointeridx, 
        [|nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) pointervl = (Vint32 pointeridx)|] **
        (([|Int.unsigned pointeridx >= 255|] ** [|v = Some(Vint32 ($SLOT_RANGE_OVERFLOW)) /\ priotbl''' = priotbl /\
        pointervl' = pointervl|])\\//
        ([|Int.unsigned pointeridx < 255|] **  [|v = Some(Vint32 ($CNODE_NONE_FAULT))|] **
        [|pointervl' = update_nth_val (Z.to_nat(Int.unsigned destTask_Prio)) pointervl (Vint32 (Int.add pointeridx (Int.repr 1)))|] **
        [|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat (Int.unsigned pointeridx)) priotbl
        ($CAP_OBJECT_TYPE , (categorycontent_val, origin_right, categoryobject_val)))|] **
        [|priotbl'' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl'
        ($0 , ($0, categoryright_val, Vnull)))|]  ** 
        [|priotbl''' = (update_nth_cspace_slots_type (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl''
        ($ SLOT_NULL_CAP))|] 
        )))
         \\//[|idxz <> SLOT_NULL_CAP|] **(
        [|v = Some(Vint32 ($CNODE_NONE_FAULT))|] **
        [|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat idxz) priotbl
        ($CAP_OBJECT_TYPE , (categorycontent_val, origin_right, categoryobject_val)))|] ** 
        [|priotbl'' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl'
        ($0 , ($0, categoryright_val, Vnull)))|] **
        [|priotbl''' = (update_nth_cspace_slots_type (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl''
        ($ SLOT_NULL_CAP))|] **  [|pointervl' = pointervl|]
        ))
    ))
    )
    )).  *)

Definition ucos_CNode_CopyPost'(vl:vallist) (v: option val)(logicl:list logicvar) ct:=
  EX destTask_Prio srcTask_Prio func_capability er s b i cs isr
  ptrvl priotbl  priotbl' cspacels pointervl pointervl'  captype_val categorycontent_val categoryright_val 
  categoryobject_val  origin_right origin_object,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  [| nth_val 0 vl = Some (Vint32 destTask_Prio) |] **
  [| nth_val 1 vl = Some (Vint32 srcTask_Prio) |] **
  [| nth_val 2 vl = Some (Vint32 func_capability) |] **
  AOSCSpaceObjectPointer pointervl' ** 
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
  AOSCSpacePrioTbl (b, i) ptrvl priotbl' cspacels ** 
  [|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er)::
  (logic_cspacel priotbl) :: (logic_lv pointervl)::(logic_code s) ::(logic_abscap cspacels):: (logic_lv ptrvl)::nil|] **
  p_local OSLInv ct init_lg ** (
    [|nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl = Vnull \/
    nth_val' (Z.to_nat(Int.unsigned srcTask_Prio)) ptrvl = Vnull|] ** [|v = Some(Vint32(Int.repr CNODE_COPY_FAILURE))/\priotbl' = priotbl /\ pointervl' = pointervl|] \\//
    ([|nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl <> Vnull /\
    nth_val' (Z.to_nat(Int.unsigned srcTask_Prio)) ptrvl <> Vnull|] **
    [|get_capability (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) 
    priotbl = Some(captype_val, (categorycontent_val, categoryright_val, categoryobject_val))|] **
    (
    ([|(Int.unsigned captype_val <> CAP_CATEGORY_TYPE) /\ (Int.unsigned captype_val <> CAP_OBJECT_TYPE)|]
    ** [|v = Some(Vint32 ($CNODE_COPY_FAILURE))|]
    ** [|priotbl' = priotbl /\ pointervl' = pointervl|]) \\//(
    [|(Int.unsigned captype_val = CAP_CATEGORY_TYPE)|] **
    [|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl
    ($CAP_CATEGORY_TYPE , (categorycontent_val, categoryright_val, origin_object)))|] ** 
    [|pointervl' = pointervl|] ** [|v = Some(Vint32 ($CNODE_NONE_FAULT))|]
    ) \\// ([|(Int.unsigned captype_val = CAP_OBJECT_TYPE)|] **
      (EX idxval idxz,
      GetObjSlotRetval destTask_Prio ptrvl pointervl priotbl categoryobject_val idxval **
        [|idxz = Int.unsigned (Vint32_inj(val_inj idxval))|] **(
       [|idxz = SLOT_NULL_CAP|] ** (
        EX pointeridx, 
        [|nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) pointervl = (Vint32 pointeridx)|] **
        (([|Int.unsigned pointeridx >= 255|] ** [|v = Some(Vint32 ($SLOT_RANGE_OVERFLOW)) /\ priotbl' = priotbl /\
        pointervl' = pointervl|])\\//
        ([|Int.unsigned pointeridx < 255|] **  [|v = Some(Vint32 ($CNODE_NONE_FAULT))|] **
        [|pointervl' = update_nth_val (Z.to_nat(Int.unsigned destTask_Prio)) pointervl (Vint32 (Int.add pointeridx (Int.repr 1)))|] **
        [|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat (Int.unsigned pointeridx)) priotbl
        ($CAP_OBJECT_TYPE , (categorycontent_val, origin_right, categoryobject_val)))|])))
         \\//[|idxz <> SLOT_NULL_CAP|] **(
        [|v = Some(Vint32 ($CNODE_NONE_FAULT))|] **
        [|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat idxz) priotbl
        ($CAP_OBJECT_TYPE , (categorycontent_val, origin_right, categoryobject_val)))|] **  [|pointervl' = pointervl|]
        ))
    ))
    )
    )). 

Theorem ucos_CNode_CopyPostGood (vl:vallist)(v:option val) ll ct:
  GoodFunAsrt (ucos_CNode_CopyPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition ucos_CNode_CopyPost : fpost :=
  fun vl v ll ct => mkfunasrt (ucos_CNode_CopyPostGood vl v ll ct).
Definition ucos_CNode_Copy_spec : fspec :=
  (ucos_CNode_CopyPre,ucos_CNode_CopyPost,(Int8u, Tint8::Tint8::Tint32::nil)).


(*ucos_CNode_Move*)
Definition ucos_CNode_MovePre'(vl:vallist) (logicl:list logicvar) ct:=
  EX destTask_Prio srcTask_Prio func_capability  er s b i cs isr
  ptrvl priotbl cspacels pointervl,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  [| nth_val 0 vl = Some (Vint32 destTask_Prio) |] **
  [| nth_val 1 vl = Some (Vint32 srcTask_Prio) |] **
  [| nth_val 2 vl = Some (Vint32 func_capability) |] **
  AOSCSpaceObjectPointer pointervl ** 
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
  [|Int.unsigned destTask_Prio > Int.unsigned srcTask_Prio|] ** (**目标CSPACE和源CSPACE不相同*)
  AOSCSpacePrioTbl (b, i) ptrvl priotbl cspacels** 
  [|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er) ::
  (logic_cspacel priotbl) :: (logic_lv pointervl) ::(logic_code s)::(logic_abscap cspacels)::(logic_lv ptrvl)::nil|] ** 
  p_local OSLInv ct init_lg **
  [|Int.unsigned destTask_Prio < OS_LOWEST_PRIO|] **
  [|Int.unsigned srcTask_Prio < OS_LOWEST_PRIO|] **
  [|Int.unsigned func_capability < SLOT_NUM|].

Theorem ucos_CNode_MovePreGood (vl:vallist) ll ct:
  GoodFunAsrt (ucos_CNode_MovePre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition ucos_CNode_MovePre : fpre :=
  fun vl ll ct => mkfunasrt (ucos_CNode_MovePreGood vl ll ct).

Definition ucos_CNode_MovePost'(vl:vallist) (v: option val)(logicl:list logicvar) ct:=
  EX destTask_Prio srcTask_Prio func_capability er s b i cs isr
  ptrvl priotbl  priotbl'  priotbl'' priotbl''' cspacels pointervl pointervl' captype_val categorycontent_val categoryright_val 
  categoryobject_val  origin_right origin_object captype_val_dest categorycontent_val_dest categoryright_val_dest,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  [| nth_val 0 vl = Some (Vint32 destTask_Prio) |] **
  [| nth_val 1 vl = Some (Vint32 srcTask_Prio) |] **
  [| nth_val 2 vl = Some (Vint32 func_capability) |] ** 
  AOSCSpaceObjectPointer pointervl' ** 
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
  AOSCSpacePrioTbl (b, i) ptrvl priotbl''' cspacels ** 
  [|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er)::
  (logic_cspacel priotbl) :: (logic_lv pointervl)::(logic_code s)::(logic_abscap cspacels)::(logic_lv ptrvl)::nil|] **
  p_local OSLInv ct init_lg ** 
  (
    [|nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl = Vnull \/
    nth_val' (Z.to_nat(Int.unsigned srcTask_Prio)) ptrvl = Vnull|] ** [|v = Some(Vint32(Int.repr CNODE_MOVE_FAILURE))/\priotbl''' = priotbl /\ pointervl' = pointervl|] \\//
    ([|nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl <> Vnull /\
    nth_val' (Z.to_nat(Int.unsigned srcTask_Prio)) ptrvl <> Vnull|] **
    [|get_capability (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) 
    priotbl = Some(captype_val, (categorycontent_val, categoryright_val, categoryobject_val))|] **
    [|get_capability (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) 
    priotbl = Some(captype_val_dest, (categorycontent_val_dest, categoryright_val_dest, origin_object))|] **
    (
    ([|(Int.unsigned captype_val <> CAP_CATEGORY_TYPE) /\ (Int.unsigned captype_val <> CAP_OBJECT_TYPE)|]
    ** [|v = Some(Vint32 ($CNODE_MOVE_FAILURE))|]
    ** [|priotbl''' = priotbl /\ pointervl' = pointervl|]) \\//(
   [|(Int.unsigned captype_val = CAP_CATEGORY_TYPE)|] **
  [|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl
  ($CAP_CATEGORY_TYPE , (categorycontent_val, categoryright_val, origin_object)))|] **
  [|priotbl'' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl'
  ($0 , ($0, $0, categoryobject_val)))|] **
  [|priotbl''' = (update_nth_cspace_slots_type (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl''
  ($ SLOT_NULL_CAP))|] **
  [|pointervl' = pointervl|] ** [|v = Some(Vint32 ($CNODE_NONE_FAULT))|]
    ) \\// ([|(Int.unsigned captype_val = CAP_OBJECT_TYPE)|] **
      (EX idxval idxz,
      GetObjSlotRetval destTask_Prio ptrvl pointervl priotbl categoryobject_val idxval **
        [| idxz = Int.unsigned (Vint32_inj(val_inj idxval))|] **(
       [|idxz = SLOT_NULL_CAP|] ** (
        EX pointeridx, 
        [|nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) pointervl = (Vint32 pointeridx)|] **
        (([|Int.unsigned pointeridx >= 255|] ** [|v = Some(Vint32 ($SLOT_RANGE_OVERFLOW)) /\ priotbl''' = priotbl /\
        pointervl' = pointervl|])\\//
        ([|Int.unsigned pointeridx < 255|] **  [|v = Some(Vint32 ($CNODE_NONE_FAULT))|] **
        [|pointervl' = update_nth_val (Z.to_nat(Int.unsigned destTask_Prio)) pointervl (Vint32 (Int.add pointeridx (Int.repr 1)))|] **
        [|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat (Int.unsigned pointeridx)) priotbl
        ($CAP_OBJECT_TYPE , (categorycontent_val, origin_right, categoryobject_val)))|]  **
        [|priotbl'' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl'
        ($0 , ($0, categoryright_val, Vnull)))|]  ** 
        [|priotbl''' = (update_nth_cspace_slots_type (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl''
        ($ SLOT_NULL_CAP))|])))
         \\//[|idxz <> SLOT_NULL_CAP|] **(
        [|v = Some(Vint32 ($CNODE_NONE_FAULT))|] **
        [|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat idxz) priotbl
        ($CAP_OBJECT_TYPE , (categorycontent_val, origin_right, categoryobject_val)))|]
        ** [|priotbl'' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl'
        ($0 , ($0, categoryright_val, Vnull)))|] **
        [|priotbl''' = (update_nth_cspace_slots_type (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl''
        ($ SLOT_NULL_CAP))|] **  [|pointervl' = pointervl|]
        ))
    ))
    )
    )).  

Theorem ucos_CNode_MovePostGood (vl:vallist)(v:option val) ll ct:
  GoodFunAsrt (ucos_CNode_MovePost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition ucos_CNode_MovePost : fpost :=
  fun vl v ll ct => mkfunasrt (ucos_CNode_MovePostGood vl v ll ct).
Definition ucos_CNode_Move_spec : fspec :=
  (ucos_CNode_MovePre,ucos_CNode_MovePost,(Int8u, Tint8::Tint8::Tint32::nil)).



(*ucos_CNode_Delete*)
Definition ucos_CNode_DeletePre'(vl:vallist) (logicl:list logicvar) ct:=
  EX destTask_Prio func_capability er s cs isr ptrvl priotbl b i cspacels,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  [| nth_val 0 vl = Some (Vint32 destTask_Prio) |] **
  [| nth_val 1 vl = Some (Vint32 func_capability) |] **
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
  AOSCSpacePrioTbl (b, i) ptrvl priotbl cspacels** 
  [|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er) :: (logic_cspacel priotbl) ::
  (logic_code s) ::(logic_abscap cspacels)::(logic_lv ptrvl)::nil|] **
  p_local OSLInv ct init_lg.

Theorem ucos_CNode_DeletePreGood (vl:vallist) ll ct:
  GoodFunAsrt (ucos_CNode_DeletePre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition ucos_CNode_DeletePre : fpre :=
  fun vl ll ct => mkfunasrt (ucos_CNode_DeletePreGood vl ll ct).

Definition ucos_CNode_DeletePost'(vl:vallist) (v: option val) (logicl:list logicvar) ct:=
  EX destTask_Prio func_capability er s cs isr ptrvl priotbl b i cspacels priotbl' priotbl''
  captype_val x y z,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  [| nth_val 0 vl = Some (Vint32 destTask_Prio) |] **
  [| nth_val 1 vl = Some (Vint32 func_capability) |] **
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
  AOSCSpacePrioTbl (b, i) ptrvl priotbl'' cspacels**
  [|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er) :: (logic_cspacel priotbl) ::
  (logic_code s)::(logic_abscap cspacels)::(logic_lv ptrvl)::nil|] ** 
  p_local OSLInv ct init_lg ** 
  ([|(Int.unsigned func_capability >= SLOT_NUM)
  \/(Int.unsigned destTask_Prio >= 64) \/(nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl = Vnull)
  |] ** [|v = Some (Vint32 ($ CNODE_DELETE_FAILURE ))|]** [|priotbl'' = priotbl|]\\//
  ([|(Int.unsigned func_capability < SLOT_NUM)
  /\Int.unsigned destTask_Prio < 64 /\nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl <> Vnull|] **
  [|get_capability (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) 
  priotbl = Some(captype_val, (x, y, z))|] **
  ([|(Int.unsigned captype_val) <> CAP_CATEGORY_TYPE /\ (Int.unsigned captype_val) <> CAP_OBJECT_TYPE|] 
  **[|v = Some (Vint32 ($ CNODE_DELETE_FAILURE ))|] ** [|priotbl'' = priotbl|]
  \\// [|priotbl' = update_nth_cspace_slots_type (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl
  ($ SLOT_NULL_CAP)|] **(
  [|Int.unsigned captype_val = CAP_CATEGORY_TYPE|] **
  [|priotbl'' = update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl'
  ($0, ($0, $0, z))|] **[|v = Some (Vint32 ($ CNODE_NONE_FAULT))|] \\//
  [|Int.unsigned captype_val = CAP_OBJECT_TYPE|] **
  [|priotbl'' = update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl'
  ($0, ($0, y, Vnull))|] **[|v = Some (Vint32 ($ CNODE_NONE_FAULT))|] 
  )))).

Theorem ucos_CNode_DeletePostGood (vl:vallist) v ll ct:
  GoodFunAsrt (ucos_CNode_DeletePost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition ucos_CNode_DeletePost : fpost :=
  fun vl v ll ct => mkfunasrt (ucos_CNode_DeletePostGood vl v ll ct).
Definition ucos_CNode_Delete_spec : fspec :=
  (ucos_CNode_DeletePre,ucos_CNode_DeletePost,(Int8u, Tint8::Tint32::nil)).


(*ucos_CNode_Mutate*)
Definition ucos_CNode_MutatePre'(vl:vallist) (logicl:list logicvar) ct:=
  EX destTask_Prio srcTask_Prio func_capability rights er s cs isr ptrvl priotbl b i cspacels,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  [| nth_val 0 vl = Some (Vint32 destTask_Prio) |] **
  [| nth_val 1 vl = Some (Vint32 srcTask_Prio) |] **
  [| nth_val 2 vl = Some (Vint32 func_capability)|] **
  [| nth_val 3 vl = Some (Vint32 rights)|] ** 
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
  AOSCSpacePrioTbl (b, i) ptrvl priotbl cspacels** 
  [|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er) :: (logic_cspacel priotbl) ::
  (logic_code s)::(logic_abscap cspacels)::(logic_lv ptrvl)::nil|] **
  [|Int.unsigned destTask_Prio > Int.unsigned srcTask_Prio|] **
  p_local OSLInv ct init_lg.

Theorem ucos_CNode_MutatePreGood (vl:vallist) ll ct:
  GoodFunAsrt (ucos_CNode_MutatePre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition ucos_CNode_MutatePre : fpre :=
  fun vl ll ct => mkfunasrt (ucos_CNode_MutatePreGood vl ll ct).

Definition ucos_CNode_MutatePost'(vl:vallist)(v: option val)(logicl:list logicvar) ct:=
  EX destTask_Prio srcTask_Prio func_capability rights er s cs isr ptrvl priotbl b i cspacels
  captype_val categorycontent_val categoryright_val z priotbl' priotbl'' priotbl'''
  captype_val_dest categorycontent_val_dest categoryright_val_dest z_dest,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  [| nth_val 0 vl = Some (Vint32 destTask_Prio) |] **
  [| nth_val 1 vl = Some (Vint32 srcTask_Prio) |] **
  [| nth_val 2 vl = Some (Vint32 func_capability)|] **
  [| nth_val 3 vl = Some (Vint32 rights)|] ** 
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
  AOSCSpacePrioTbl (b, i) ptrvl priotbl''' cspacels** 
  [|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er) :: (logic_cspacel priotbl) ::
  (logic_code s)::(logic_abscap cspacels)::(logic_lv ptrvl)::nil|] **
  p_local OSLInv ct init_lg **(
  ([|(CAP_NULL_CLASS > Int.unsigned func_capability \/ Int.unsigned func_capability > CAP_CHANNEL_CLASS)
  \/(Int.unsigned destTask_Prio >= 64 \/ Int.unsigned srcTask_Prio >= 64) \/(nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl = Vnull \/ nth_val' (Z.to_nat(Int.unsigned srcTask_Prio)) ptrvl = Vnull)
  |] ** [|v = Some (Vint32 ($ CNODE_MUTATE_FAILURE ))|] **[|priotbl'''= priotbl|])\\//(
  [|(CAP_NULL_CLASS <=Int.unsigned func_capability <= CAP_CHANNEL_CLASS)
  /\(Int.unsigned destTask_Prio < 64 /\ Int.unsigned srcTask_Prio < 64) /\(nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl <> Vnull /\ nth_val' (Z.to_nat(Int.unsigned srcTask_Prio)) ptrvl <> Vnull)|] **
  [|get_capability (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) 
  priotbl = Some(captype_val, (categorycontent_val, categoryright_val, z))|] **
  [|get_capability (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) 
  priotbl = Some(captype_val_dest, (categorycontent_val_dest, categoryright_val_dest, z_dest))|] **
  ([|captype_val <> ($ CAP_CATEGORY_TYPE)\/ Int.and (Int.not categoryright_val) rights <> $0
      \/ categoryright_val = rights|] ** [|v = Some (Vint32 ($ CNODE_MUTATE_FAILURE ))|] ** [|priotbl'''=priotbl|]\\//
    [|captype_val = ($ CAP_CATEGORY_TYPE) /\ Int.and (Int.not categoryright_val) rights = $0
    /\ categoryright_val <> rights|] ** 
    [|priotbl''' = update_nth_cspace_slots_type (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl''
    ($ SLOT_NULL_CAP)|] ** 
    [|priotbl'' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl'
    (captype_val , (categorycontent_val, Int.and (categoryright_val)(Int.not rights), z)))|] **
    (*上面两句是关于srcTaskPrio的变化*)
    [|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl
    ($CAP_CATEGORY_TYPE , (categorycontent_val, rights, z_dest)))|] ** (*这个是针对destTask_Prio的变化*)
    [|v = Some (Vint32 ($ CNODE_NONE_FAULT))|] 
  ))).
      
Theorem ucos_CNode_MutatePostGood (vl:vallist) v ll ct:
  GoodFunAsrt (ucos_CNode_MutatePost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition ucos_CNode_MutatePost : fpost :=
  fun vl v ll ct => mkfunasrt (ucos_CNode_MutatePostGood vl v ll ct).
Definition ucos_CNode_Mutate_spec : fspec :=
  (ucos_CNode_MutatePre,ucos_CNode_MutatePost,(Int8u, Tint8::Tint8::Tint32::Tint32::nil)).

(*Check_Cap_Type*)
Definition Check_Cap_TypePre'(vl:vallist) (logicl:list logicvar) ct:=
  EX func_capability func_capType prio er s cs isr b i b1 i1 b2 i2 b3 i3 
  ptrvl priotbl cspacels semvl mutexvl mqvl pointervl
  vl' rtbl tcbls ptls vhold,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  [| nth_val 0 vl = Some (Vint32 func_capability) |] **
  [| nth_val 1 vl = Some (Vint32 func_capType) |] **
  [| nth_val 2 vl = Some (Vint32 prio) |] **
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
  AOSCSpacePrioTbl (b, i) ptrvl priotbl cspacels** 
  ASeminfo (b1, i1) semvl ** 
  APthreadMutex(b2, i2) mutexvl ** 
  AMqAttr (b3, i3) mqvl **
  AOSCSpaceObjectPointer pointervl ** 
  AOSTCBPrioTbl vl' rtbl tcbls ptls vhold **
  [|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er)::(logic_lv ptrvl) :: (logic_cspacel priotbl) :: (logic_lv pointervl) ::
  (logic_code s)::(logic_abscap cspacels)::(logic_lv rtbl)::(logic_abstcb tcbls)::(logic_addrval vhold)::
  (logic_llv mqvl)::(logic_llv mutexvl)::(logic_llv semvl)::(logic_block b) ::(logic_block b1)::(logic_block b2)::
  (logic_block b3)::(logic_intaddr i) :: (logic_intaddr i1)::(logic_intaddr i2)::(logic_intaddr i3)::
  (logic_lv vl')::(logic_lv rtbl)::(logic_abstcb tcbls)::
  (logic_absptb ptls)::(logic_addrval vhold)::nil|] **
  p_local OSLInv ct init_lg **
  [|Int.unsigned prio < OS_LOWEST_PRIO|].
  (*这个是由于调用check_cap_type的api函数都会做这个判断*)

Theorem Check_Cap_TypePreGood (vl:vallist) ll ct:
  GoodFunAsrt (Check_Cap_TypePre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition Check_Cap_TypePre : fpre :=
  fun vl ll ct => mkfunasrt (Check_Cap_TypePreGood vl ll ct).


Definition nth_seminfo_pevent n vl:=
    match nth_vallist n vl with 
    | Some vl' => nth_val' 7%nat vl' 
    | _ => Vundef
    end. 
Definition nth_mutex_pevent n vl:=
  match nth_vallist n vl with 
  | Some vl' => nth_val' 8%nat vl' 
  | _ => Vundef
  end. 
Definition nth_q_pevent n vl:=
  match nth_vallist n vl with 
  | Some vl' => nth_val' 5%nat vl' 
  | _ => Vundef
  end. 
(*Check_Cap_Type*)
Definition Check_Cap_TypePost'(vl:vallist)(v: option val) (logicl:list logicvar) ct:=
  EX func_capability func_capType prio er s cs isr b i b1 i1 b2 i2 b3 i3 
  ptrvl priotbl cspacels semvl mutexvl mqvl pointervl
  vl' rtbl tcbls ptls vhold,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  [| nth_val 0 vl = Some (Vint32 func_capability) |] **
  [| nth_val 1 vl = Some (Vint32 func_capType) |] **
  [| nth_val 2 vl = Some (Vint32 prio) |] **
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
  AOSCSpacePrioTbl (b, i) ptrvl priotbl cspacels** 
  ASeminfo (b1, i1) semvl ** 
  APthreadMutex(b2, i2) mutexvl ** 
  AMqAttr (b3, i3) mqvl **
  AOSCSpaceObjectPointer pointervl ** 
  AOSTCBPrioTbl vl' rtbl tcbls ptls vhold **
  [|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er)::(logic_lv ptrvl) :: (logic_cspacel priotbl) :: (logic_lv pointervl) ::
  (logic_code s)::(logic_abscap cspacels)::(logic_lv rtbl)::(logic_abstcb tcbls)::(logic_addrval vhold)::
  (logic_llv mqvl)::(logic_llv mutexvl)::(logic_llv semvl)::(logic_block b) ::(logic_block b1)::(logic_block b2)::
  (logic_block b3)::(logic_intaddr i)::(logic_intaddr i1)::(logic_intaddr i2)::(logic_intaddr i3)::
  (logic_lv vl')::(logic_lv rtbl)::(logic_abstcb tcbls)::
  (logic_absptb ptls)::(logic_addrval vhold)::nil|] **
  p_local OSLInv ct init_lg  **(
  [|Int.unsigned func_capType = CAP_FUNCTION_TYPE|] ** 
  ([|Int.unsigned func_capability <= CAP_CHANNEL_CLASS|] ** [|v = Some(Vint32 func_capability)|]
  \\// [|Int.unsigned func_capability > CAP_CHANNEL_CLASS|] ** [|v = Some(Vint32 (Int.repr SLOT_NUM))|])
  \\// [|(Int.unsigned func_capType = CAP_SEM_TYPE \/Int.unsigned func_capType = CAP_MUTEX_TYPE \/ Int.unsigned func_capType = CAP_Q_TYPE) /\ (Int.unsigned func_capability < OS_USER_MAX_EVENTS / 3)|] **
  (
  [|Int.unsigned func_capType = CAP_SEM_TYPE|] **(
    EX sem_pevent, [|sem_pevent = nth_seminfo_pevent (Z.to_nat(Int.unsigned func_capability)) semvl|] **
    ([|sem_pevent = Vnull|] ** [|v = Some(Vint32 (Int.repr SLOT_NUM))|]
    \\//[|sem_pevent <> Vnull|] ** (
      EX idxval idxz,
      GetObjSlotRetval prio ptrvl pointervl priotbl sem_pevent idxval **
      [|(Vint32 (Int.repr idxz)) = (val_inj idxval)|] ** (
        [|idxz = SLOT_NULL_CAP|] ** [|v = Some(Vint32(Int.repr SLOT_NUM))|] \\//
        [|idxz <> SLOT_NULL_CAP|] ** [|v = idxval|]
      )
    )
    )
  ) \\//[|Int.unsigned func_capType = CAP_MUTEX_TYPE|] **(
    EX mutex_pevent, [|mutex_pevent = nth_mutex_pevent (Z.to_nat(Int.unsigned func_capability)) mutexvl|] **
    ([|mutex_pevent = Vnull|] ** [|v = Some(Vint32 (Int.repr SLOT_NUM))|]
    \\//[|mutex_pevent <> Vnull|] ** (
      EX idxval idxz,
      GetObjSlotRetval prio ptrvl pointervl priotbl mutex_pevent idxval **
      [|(Vint32 (Int.repr idxz)) = (val_inj idxval)|] ** (
        [|idxz = SLOT_NULL_CAP|] ** [|v = Some(Vint32(Int.repr SLOT_NUM))|] \\//
        [|idxz <> SLOT_NULL_CAP|] ** [|v = idxval|]
      )
    )
    )
  )\\//[|Int.unsigned func_capType = CAP_Q_TYPE|] **(
    EX mq_pevent, [|mq_pevent = nth_q_pevent (Z.to_nat(Int.unsigned func_capability)) mqvl|] **
    ([|mq_pevent = Vnull|] ** [|v = Some(Vint32 (Int.repr SLOT_NUM))|]
    \\//[|mq_pevent <> Vnull|] ** (
      EX idxval idxz,
      GetObjSlotRetval prio ptrvl pointervl priotbl mq_pevent idxval **
      [|(Vint32 (Int.repr idxz)) = (val_inj idxval)|] ** (
        [|idxz = SLOT_NULL_CAP|] ** [|v = Some(Vint32(Int.repr SLOT_NUM))|] \\//
        [|idxz <> SLOT_NULL_CAP|] ** [|v = idxval|]
      )
    )
    )
  )
  ) \\//[|Int.unsigned func_capType = CAP_TASK_TYPE /\ Int.unsigned func_capability < OS_STAT_PRIO /\ 
  Int.unsigned func_capability  > 0|] **(
    EX tcbptr, [|tcbptr = nth_val' (Z.to_nat(Int.unsigned func_capability)) vl'|] **
    ([|tcbptr = Vnull|] ** [|v = Some(Vint32 (Int.repr SLOT_NUM))|]
    \\//[|tcbptr <> Vnull|] ** (
      EX idxval idxz,
      GetObjSlotRetval prio ptrvl pointervl priotbl tcbptr idxval **
      [|(Vint32 (Int.repr idxz)) = (val_inj idxval)|] ** (
        [|idxz = SLOT_NULL_CAP|] ** [|v = Some(Vint32(Int.repr SLOT_NUM))|] \\//
        [|idxz <> SLOT_NULL_CAP|] ** [|v = idxval|]
      )
    )
    )
  ) \\//[|Int.unsigned func_capType <> CAP_FUNCTION_TYPE /\ ~((Int.unsigned func_capType = CAP_SEM_TYPE \/Int.unsigned func_capType = CAP_MUTEX_TYPE \/ Int.unsigned func_capType = CAP_Q_TYPE) /\ (Int.unsigned func_capability <  OS_USER_MAX_EVENTS / 3)) /\
  ~(Int.unsigned func_capType = CAP_TASK_TYPE /\ Int.unsigned func_capability < OS_STAT_PRIO /\ 
  Int.unsigned func_capability  > 0)|] ** [|v = Some (Vint32 (Int.repr SLOT_NUM))|]
  ).

Theorem Check_Cap_TypePostGood (vl:vallist) v ll ct:
  GoodFunAsrt (Check_Cap_TypePost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition Check_Cap_TypePost : fpost :=
  fun vl v ll ct => mkfunasrt (Check_Cap_TypePostGood vl v ll ct).
Definition Check_Cap_Type_spec : fspec :=
  (Check_Cap_TypePre,Check_Cap_TypePost,(Int32u, Tint32::Tint8::Tint8::nil)).

  
(*Check_Cap_Type weak post spec*)

(*Check_Cap_Type*)
Definition Check_Cap_TypePost''(vl:vallist)(v: option val) (logicl:list logicvar) ct:=
  EX func_capability func_capType prio er s cs isr b i b1 i1 b2 i2 b3 i3 
  ptrvl priotbl cspacels semvl mutexvl mqvl pointervl
  vl' rtbl tcbls ptls vhold,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  [| nth_val 0 vl = Some (Vint32 func_capability) |] **
  [| nth_val 1 vl = Some (Vint32 func_capType) |] **
  [| nth_val 2 vl = Some (Vint32 prio) |] **
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
  AOSCSpacePrioTbl (b, i) ptrvl priotbl cspacels** 
  ASeminfo (b1, i1) semvl ** 
  APthreadMutex(b2, i2) mutexvl ** 
  AMqAttr (b3, i3) mqvl **
  AOSCSpaceObjectPointer pointervl ** 
  (* GV OSPrioCur @ (Tint8) |-> Vint32 v' ** [| Int.unsigned v' <= 63 |] **  *)
  AOSTCBPrioTbl vl' rtbl tcbls ptls vhold **
  [|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er)::(logic_lv ptrvl) :: (logic_cspacel priotbl) :: (logic_lv pointervl) ::
  (logic_code s)::(logic_abscap cspacels)::(logic_lv rtbl)::(logic_abstcb tcbls)::(logic_addrval vhold)::
  (logic_llv mqvl)::(logic_llv mutexvl)::(logic_llv semvl)::(logic_block b) ::(logic_block b1)::(logic_block b2)::
  (logic_block b3)::(logic_intaddr i) :: (logic_intaddr i1)::(logic_intaddr i2)::(logic_intaddr i3)::
  (logic_lv vl')::(logic_lv rtbl)::(logic_abstcb tcbls)::
  (logic_absptb ptls)::(logic_addrval vhold)::nil|] **
  p_local OSLInv ct init_lg  **(
  [|v = Some(Vint32 (Int.repr SLOT_NUM))|] \\//
  [|(exists ret, v = Some(Vint32(Int.repr ret)) /\ 0 <= ret < 255) /\
  ((Int.unsigned func_capType = CAP_FUNCTION_TYPE /\ Int.unsigned func_capability <= CAP_CHANNEL_CLASS) \/
  ((Int.unsigned func_capType = CAP_SEM_TYPE \/ Int.unsigned func_capType = CAP_MUTEX_TYPE \/ Int.unsigned func_capType = CAP_Q_TYPE) /\
  Int.unsigned func_capability <  OS_USER_MAX_EVENTS / 3) \/
  (Int.unsigned func_capType = CAP_TASK_TYPE /\ Int.unsigned func_capability < OS_STAT_PRIO))
  |]
  ).

Theorem Check_Cap_TypeWeakPostGood (vl:vallist) v ll ct:
  GoodFunAsrt (Check_Cap_TypePost'' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition Check_Cap_TypeWeakPost : fpost :=
  fun vl v ll ct => mkfunasrt (Check_Cap_TypeWeakPostGood vl v ll ct).
Definition Check_Cap_Type_spec_weak : fspec :=
  (Check_Cap_TypePre,Check_Cap_TypeWeakPost,(Int32u, Tint32::Tint8::Tint8::nil)).

  
(*CNode_delete_recursive*)
Require Import Lia.
Lemma nth_val_exists:
  forall vl n,
  (n < (length vl))%nat ->
  exists v, nth_cspace n vl = Some v.
Proof.
  induction vl; destruct n;intros.
  simpl in H. lia. 
  simpl in H. lia.
  eexists. simpl. eauto. 
  simpl in H. 
  assert(n < (length vl))%nat by lia.
  eapply IHvl in H0.
  destruct H0.
  exists x. 
  simpl. auto.
Qed. 

Lemma nth_val_none:
forall vl n,
  (n >= (length vl))%nat ->
  nth_val n vl = None.
Proof.
  induction vl; destruct n; intros; simpl; auto. 
  simpl in H. lia.
  simpl in H. 
  assert(n >= (length vl))%nat by lia.
  eapply IHvl in H0.
  auto. 
Qed.
Lemma nth_val'2nth_val_vptr:
  forall n rtbl x,
    nth_val' n rtbl = Vptr x ->
    nth_val n rtbl = Some (Vptr x).
Proof.
  intros.
  inductions n;
  simpl in *;  destruct rtbl; simpl in *;tryfalse; try subst; auto.

Qed.
Lemma reverse_map_len:
  forall vl n map,
  children_not_null vl n ->
  length (reverse_map map vl) = n. 
Proof.
  induction vl; destruct n; intros. 
  simpl in H. simpl. auto.  
  unfolds in H. destruct H.
  lets Hx: H 0%nat. 
  assert((0 <= 0 < S n)%nat) by lia.
  lets H1_bak: H1.
  eapply Hx in H1.
  destruct H1.
  eapply nth_val'2nth_val_vptr in H1.
  simpl in H1. tryfalse.
  unfolds in H. destruct H. 
  lets Hx: H0 0%nat.
  assert((0 <= 0 <
  length (a :: vl))%nat). simpl. lia.
  eapply Hx in H1. 
  simpl in H1. subst a. 
  simpl. 
  assert(children_not_null vl 0%nat).
  unfolds. 
  split. intros. lia.
  simpl in H0. 
  intros.
  assert(0 <= (S i) < S(length vl))%nat by lia.
  eapply H0 in H2.
  simpl in H2. auto. 
  eapply IHvl; eauto. 
  simpl. 
  lets H_bak: H. 
  unfolds in H. simpl in H. 
  destruct H. 
  lets Hx: H 0%nat. 
  assert((0 <= 0 < S n)%nat) by lia.
  eapply Hx in H1. destruct H1.
  simpl in H1. subst a. simpl. 
  assert(children_not_null vl n).
  unfolds. splits; intros.
  assert(0 <= (S i) < (S n))%nat by lia.
  eapply H in H2.
  simpl in H2. eauto. 
  assert((S n <=(S i)< S (length vl))%nat) by lia.
  eapply H0 in H2.
  simpl in H2. eauto. 
  eapply IHvl in H1; eauto.
Qed.
 



Lemma wellform_descendents_trans1:
  forall index childlist ls map,
  wellform_descendents index childlist ls map ->
  exists childs,
    childlist = index :: childs /\
    wellform_descendents_list (child index ls map) childs ls map.
Proof.
  intros.
  inversion H.
  exists descs.
  auto.
Qed.

Lemma wellform_descendents_trans_cons:
  forall node rest descs ls map,
  wellform_descendents_list (node :: rest) descs ls map ->
  exists descs1 descs2,
    descs = descs1 ++ descs2 /\
    intersection descs1 descs2 = false /\
    wellform_descendents node descs1 ls map /\
    wellform_descendents_list rest descs2 ls map.
Proof.
  intros.
  inversion H.
  exists desc1 desc2.
  auto.
Qed.

Lemma  intersection_nil: 
  forall l, 
  intersection l nil = false.
Proof.
  intros.
  induction l. simpl. auto.
  simpl. auto.
Qed.

Lemma  intersection_acc: 
  forall l a l1,
  intersection (a::l) l1   = false ->
  intersection l l1 = false /\ contains l1 a = false.
Proof.
  intros. 
  destruct l1. 
  simpl. auto.
  simpl in H. 
  destruct (Int.eq i a) eqn: Heq1.
  destruct (intersection l (i :: l1)) eqn: Heq2.
  simpl in H. tryfalse.
  simpl in H. tryfalse.
  eapply orb_false_elim in H. 
  split. 
  destruct H. auto.
  destruct H. simpl. rewrite Heq1.
  auto.
Qed.

Lemma contains_split_left:
  forall l1 l2 a,
  contains (l1 ++ l2) a = false ->
  contains l1 a = false.
Proof.
  induction l1. intros.
  simpl. auto.
  intros. 
  rewrite <- app_comm_cons in H. 
  simpl in H. 
  destruct (Int.eq a a0) eqn: Heq1.
  tryfalse.
  eapply IHl1 in H. 
  simpl. rewrite Heq1. auto.
Qed.

Lemma contains_split_right:
  forall l1 l2 a,
  contains (l1 ++ l2) a = false ->
  contains l2 a = false.
Proof.
  induction l1. intros.
  simpl. auto.
  intros. 
  rewrite <- app_comm_cons in H. 
  simpl in H. 
  destruct (Int.eq a a0) eqn: Heq1.
  tryfalse.
  eapply IHl1 in H. 
  auto. 
Qed.

Lemma intersection_split_left: 
  forall l l1 l2,
  intersection l (l1 ++ l2) = false ->
  intersection l l1 = false.
Proof.
  induction l. 
  intros. simpl. auto.
  intros. 
  simpl. 
  eapply intersection_acc in H. 
  destruct H. eapply IHl in H. 
  rewrite H. 
  eapply contains_split_left in H0.
  rewrite H0. simpl. auto.
Qed.

Lemma intersection_split_right: 
  forall l l1 l2,
  intersection l (l1 ++ l2) = false ->
  intersection l l2 = false.
Proof.
  induction l. 
  intros. simpl. auto.
  intros. 
  simpl. 
  eapply intersection_acc in H. 
  destruct H. eapply IHl in H. 
  rewrite H. 
  eapply contains_split_right in H0.
  rewrite H0. simpl. auto.
Qed.
Lemma intersection_append:
  forall l1 l2 l,
  intersection l1 l = false ->
  intersection l2 l = false ->
  intersection (l1 ++ l2) l = false.
Proof.
  induction l1; intros.
  simpl. auto. 
  simpl in H. 
  simpl. 
  destruct (contains l a);
  destruct (intersection l1 l) eqn: Heq.
  simpl in H. tryfalse.
  simpl in H. tryfalse.
  simpl in H. tryfalse.
  simpl. 
  eapply IHl1; auto. 
Qed.  


Lemma wellform_descendents_trans_general:
  forall ch_head ch_x ch_rest descs ls map,
  wellform_descendents_list (ch_head ++ ch_x :: ch_rest) descs ls map ->
  exists descs1 descs2 descs3,
    descs = descs1 ++ descs2 ++ descs3 /\
    wellform_descendents_list ch_head descs1 ls map /\
    wellform_descendents ch_x descs2 ls map /\
    wellform_descendents_list ch_rest descs3 ls map /\ 
    (intersection descs1 descs2 = false) /\
    (intersection descs1 descs3 = false) /\ 
    (intersection descs2 descs3 = false).
Proof.
  intros.
  generalize dependent descs.
  induction ch_head.
  1: {
    intro descs.
    exists (@nil int32). simpl in H.
    apply wellform_descendents_trans_cons in H.
    destruct H as [descs1 [descs2 H]].
    destruct H as [H1 [H2 [H3 H4]]].
    exists descs1 descs2.
    simpl. apply conj. apply H1.
    apply conj. apply wellform_descendents_list_leaf.
    apply conj. apply H3.
    rewrite H2.
    splits; auto.
  }
  intros descs H.
  simpl in H.
  apply wellform_descendents_trans_cons in H.
  destruct H as [descs1 [descs2 H]].
  destruct H as [H1 [H2 [H3 H4]]].
  apply IHch_head in H4.
  destruct H4 as [descs21 [descs22 [descs23 H4]]].
  destruct H4 as [H41 [H42 [H43 H44]]].
  rewrite H1. rewrite H41.
  exists (descs1 ++ descs21). exists descs22.
  exists descs23. apply conj.
  rewrite app_assoc. auto.
  apply conj. apply wellform_descendents_list_cons.
  apply H3. apply H42.
  rewrite H41 in H2. 
  eapply intersection_split_left in H2. auto.
  apply conj. apply H43.
  destruct H44.
  destruct H0. destruct H4.
  splits; auto. 
  assert(intersection descs1 descs22 = false).
  clear -H41 H2.
  rewrite H41 in H2.
  eapply intersection_split_right in H2. 
  eapply intersection_split_left in H2. auto. 
  eapply intersection_append; auto. 
  assert(intersection descs1 descs23 = false).
  clear -H41 H2.
  rewrite H41 in H2.
  eapply intersection_split_right in H2. 
  eapply intersection_split_right in H2. auto.
  eapply intersection_append; auto. 
Qed.
  
Lemma wellform_descendents_trans_general2:
  forall ch_head ch_rest ch_x index childlist ls map,
  child index ls map = ch_head ++ ch_x :: ch_rest ->
  wellform_descendents index childlist ls map ->
  exists child_head childs1 childs2,
    childlist = index :: child_head ++ (childs1 ++ childs2) /\
  wellform_descendents_list ch_head child_head ls map /\
  wellform_descendents ch_x childs1 ls map /\
  wellform_descendents_list ch_rest childs2 ls map /\
  (intersection child_head childs1 = false) /\
  (intersection child_head childs2 = false) /\
  (intersection childs1 childs2 = false).
Proof.
  intros.
  apply wellform_descendents_trans1 in H0.
  destruct H0 as [childs [H0 H1]].
  rewrite H in H1.
  apply wellform_descendents_trans_general in H1.
  destruct H1 as [descs1 [descs2 [descs3 H1]]].
  destruct H1 as [H2 [H3 [H4 H5]]].
  exists descs1 descs2 descs3.
  apply conj. rewrite H0. rewrite H2. auto.
  apply conj. apply H3.
  apply conj. apply H4.
  splits.
  apply H5. 
  destruct H5. 
  destruct H5. destruct H6. auto. 
  destruct H5. destruct H5. destruct H6. auto.
  destruct H5. destruct H5. destruct H6. auto.
Qed.

(* Reset a single cspace slot *)
Definition reset_nth_cspace_slot (prio: priority) (class: nat) (ls: list cspace_val_type) :=
  match nth_cspace (Z.to_nat (Int.unsigned prio)) ls with
  | Some (cnode, c, d, e, idx) =>
    match cnode with 
    | (f, g, slotvl) =>
      match nth_slots class slotvl with 
      | Some (a, (b1, ((b2, b3), b4))) => 
      if Int.eq b1 ($CAP_CATEGORY_TYPE) then 
        (update_nth_list cspace_val_type (Z.to_nat (Int.unsigned prio)) ls
        ((f, g, (update_nth_list slot_val_type class slotvl ($SLOT_NULL_CAP, ($0, (($0, $0), b4))))), c, d, e, idx))
      else if Int.eq b1 ($CAP_OBJECT_TYPE) then 
        (update_nth_list cspace_val_type (Z.to_nat (Int.unsigned prio)) ls
        ((f, g, (update_nth_list slot_val_type class slotvl ($SLOT_NULL_CAP, ($0, (($0, b3), Vnull))))), c, d, e, idx))
      else 
      update_nth_list cspace_val_type (Z.to_nat (Int.unsigned prio)) ls
      ((f, g, (update_nth_list slot_val_type class slotvl ($SLOT_NULL_CAP, (b1, ((b2, b3), b4)))), c, d, e, idx))
      | None => ls
      end 
    end 
  | None => ls
  end.


(* Reset a list of cspace slots *)
Fixpoint reset_nthlist_cspace_slot (priols: list priority) (class: nat) (ls: list cspace_val_type) :=
  match priols with 
   | prio :: priols' => (reset_nth_cspace_slot prio class  
       (reset_nthlist_cspace_slot priols' class ls))
   | nil => ls
  end.

(*Reset all descendents of an index.
  This is defined as a relation, because wellform_descendents condition
  is required.
*)

Definition reset_nth_cspace_slot_option node  (class: nat) n_class ls ls1:=
  Check_Cap_Type_WeakRet n_class/\
  if((0 <=? n_class)%nat && (n_class <? Z.to_nat SLOT_NUM)%nat )
  then reset_nth_cspace_slot node n_class ls = ls1
  else ls = ls1.
Inductive reset_descendents_cspace_slot:
  int32 -> nat -> CSpaceptr2prioMod.map -> list cspace_val_type -> list cspace_val_type -> Prop :=
| reset_descendents_cspace_slot_neqnull:
  forall node childs ls ls1 ls2 map class,
  wellform_descendents node childs ls map ->
  (exists n_class, reset_nth_cspace_slot_option node class n_class ls ls1 )->
  reset_descendents_cspace_list_slot (child node ls map) class map ls1 ls2 ->
  reset_descendents_cspace_slot node class map ls ls2
with
(* Reset all descendents of a list of indices.
   This is defined as a relation, for the same reason as in
   reset_descendents_cspace_slot.
*)
reset_descendents_cspace_list_slot:
  list int32 -> nat -> CSpaceptr2prioMod.map -> list cspace_val_type -> list cspace_val_type -> Prop :=
| reset_descendents_cspace_list_slot_nil:
  forall class ls map,
  reset_descendents_cspace_list_slot nil class map ls ls
| reset_descendents_cspace_list_slot_cons:
  forall node rest class ls ls1 ls2 map,
  reset_descendents_cspace_slot node class map ls ls1 ->
  reset_descendents_cspace_list_slot rest class map ls1 ls2 ->
  reset_descendents_cspace_list_slot (node :: rest) class map ls ls2.


Scheme reset_descendents_cspace_slot_mut :=
  Induction for reset_descendents_cspace_slot Sort Prop
with
  reset_descendents_cspace_list_slot_mut :=
  Induction for reset_descendents_cspace_list_slot Sort Prop.

Scheme wellform_descendents_mut :=
  Induction for wellform_descendents Sort Prop
with
  wellform_descendents_list_mut :=
  Induction for wellform_descendents_list Sort Prop.

(* Lemma is specifically written in this way to enable induction *)
Lemma wellform_descendents_unique':
  forall node desc1 ls map,
    wellform_descendents node desc1 ls map ->
    forall desc2,
    wellform_descendents node desc2 ls map ->
    desc1 = desc2.
Proof.
  apply (wellform_descendents_mut
    (fun node desc1 ls map
      (pf1: wellform_descendents node desc1 ls map) => forall desc2,
      wellform_descendents node desc2 ls map ->
      desc1 = desc2)
    (fun nodes desc1 ls map
      (pf2: wellform_descendents_list nodes desc1 ls map) => forall desc2,
      wellform_descendents_list nodes desc2 ls map ->
      desc1 = desc2)
    ).
  {
    intros.
    inversion H0.
    apply H in H1.
    rewrite H1. auto.
  }
  {
    intros.
    inversion H.
    auto.
  }
  {
    intros.
    inversion H1.
    apply H in H4.
    apply H0 in H5.
    rewrite H4, H5.
    auto.
  }
Qed.




Lemma wellform_descendents_unique:
  forall node desc1 desc2 ls map,
    wellform_descendents node desc1 ls map ->
    wellform_descendents node desc2 ls map ->
    desc1 = desc2.
Proof.
  intros.
  eapply wellform_descendents_unique'; eauto.
Qed.

Lemma wellform_descendents_list_unique:
  forall nodes desc1 desc2 ls map,
    wellform_descendents_list nodes desc1 ls map ->
    wellform_descendents_list nodes desc2 ls map ->
    desc1 = desc2.
Proof.
  intros.
  generalize dependent desc1.
  generalize dependent desc2.
  induction nodes.
  {
    intros.
    inversion H.
    inversion H0.
    auto.
  }
  {
    intros.
    inversion H.
    inversion H0.
    pose proof IHnodes desc3 H4 desc5 H12 as IH1.
    pose proof wellform_descendents_unique a desc0 desc4 ls map H3 H11 as IH2.
    rewrite IH1, IH2.
    auto.
  }
Qed.


Definition child_num_of (v: option cspace_val_type):=
  match v with 
    | Some (a, b, c, d, e) => Some b
    | None => None
  end.
Definition children_val_of (v: option cspace_val_type):=
  match v with 
    | Some (a, b, c, d, e) => Some c
    | None => None
  end.


(*一些关于nth_cspace和update_nth_list的性质*)  
Lemma nth_cspace_nil:
forall x,
  nth_cspace x nil = None. 
Proof.
  intros.
  destruct x. 
  simpl. auto.
  simpl. auto.
Qed.

Lemma update_nth_cspace_eq:
  forall vl x n,
  (n < (length vl))%nat ->
  nth_cspace n (update_nth_list cspace_val_type n vl x) = Some x.
Proof.
  inductions vl; destruct n; intros.
  simpl in H. lia.
  simpl in H. lia.
  simpl. auto. 
  simpl in H. 
  assert(n < (length vl))%nat by lia. 
  eapply IHvl with(x:=x) in H0. 
  simpl. auto. 
Qed.
(*修改某个下标的cspace其他都保持不变*)
Lemma update_nth_cspace_neqrev:
  forall vl (n m : nat) x,
    (n < (length vl))%nat ->
    (m < (length vl))%nat ->
    n <> m ->
    nth_cspace n (update_nth_list cspace_val_type m vl x) = nth_cspace n vl.
Proof.
  inductions vl; destruct n; destruct m; (try lia); intros.
  simpl in H. lia.
  simpl in H. lia. 
  simpl in H. lia. 
  simpl. auto. 
  simpl. auto. 
  simpl. 
  simpl in H, H0. 
  eapply IHvl; lia.
Qed.

Lemma update_nth_slots_eq:
  forall vl x n,
  (n < (length vl))%nat ->
  nth_slots n (update_nth_list slot_val_type n vl x) = Some x.
Proof.
  inductions vl; destruct n; intros.
  simpl in H. lia.
  simpl in H. lia.
  simpl. auto. 
  simpl in H. 
  assert(n < (length vl))%nat by lia. 
  eapply IHvl with(x:=x) in H0. 
  simpl. auto. 
Qed.
(*修改某个下标的cspace其他都保持不变*)
Lemma update_nth_slots_neqrev:
  forall vl (n m : nat) x,
    (n < (length vl))%nat ->
    (m < (length vl))%nat ->
    n <> m ->
    nth_slots n (update_nth_list slot_val_type m vl x) = nth_slots n vl.
Proof.
  inductions vl; destruct n; destruct m; (try lia); intros.
  simpl in H. lia.
  simpl in H. lia. 
  simpl in H. lia. 
  simpl. auto. 
  simpl. auto. 
  simpl. 
  simpl in H, H0. 
  eapply IHvl; lia.
Qed.

Lemma nth_cspace_exists:
  forall vl n,
  (n < (length vl))%nat ->
  exists v, nth_cspace n vl = Some v.
Proof.
  induction vl; destruct n;intros.
  simpl in H. lia. 
  simpl in H. lia.
  eexists. simpl. eauto. 
  simpl in H. 
  assert(n < (length vl))%nat by lia.
  eapply IHvl in H0.
  destruct H0.
  exists x. 
  simpl. auto.
Qed. 

Lemma nth_cspace_none:
forall vl n,
  (n >= (length vl))%nat ->
  nth_cspace n vl = None.
Proof.
  induction vl; destruct n; intros; simpl; auto. 
  simpl in H. lia.
  simpl in H. 
  assert(n >= (length vl))%nat by lia.
  eapply IHvl in H0.
  auto. 
Qed.

Lemma nth_slots_none:
forall vl n,
  (n >= (length vl))%nat ->
  nth_slots n vl = None.
Proof.
  induction vl; destruct n; intros; simpl; auto. 
  simpl in H. lia.
  simpl in H. 
  assert(n >= (length vl))%nat by lia.
  eapply IHvl in H0.
  auto. 
Qed.
Lemma update_nth_cspace_remain:
  forall v vl n ,
  (n >= (length vl))%nat ->
  update_nth_list cspace_val_type n vl v = vl.
Proof.
  induction vl; destruct n; intros; simpl; auto. 
  simpl in H. lia. 
  simpl in H. 
  assert(n >= (length vl))%nat by lia.
  eapply IHvl in H0. 
  rewrite H0. auto.
Qed.


Lemma nth_cspace_head_remove: 
  forall n x l ,
  nth_cspace (S n) (x :: l) = nth_cspace n l. 
Proof.
  simpl. intros. auto. 
Qed.

Lemma update_nth_list_swap:
  forall t vl x y  v1 v2,
  (x < length vl)%nat ->
  (y < length vl)%nat ->
  x <> y ->
  update_nth_list t x (update_nth_list t y vl v2) v1 =
  update_nth_list t y (update_nth_list t x vl v1) v2.
Proof.
  induction vl; destruct x; destruct y; intros.
  tryfalse.
  simpl in H0. lia.
  simpl in H0. lia.
  simpl in H0. lia.
  intros. tryfalse.
  simpl. auto. simpl. auto.
  simpl in H, H0.
  simpl. 
  assert(x < length vl)%nat by lia.
  assert(y < length vl)%nat by lia.
  
  assert(x <> y) by lia.
  assert( update_nth_list t x
  (update_nth_list t y vl v2) v1 = 
  update_nth_list t y
     (update_nth_list t x vl v1) v2).
  eapply IHvl; eauto.
  rewrite H5. auto.
Qed.
    

(*重新增强了child_similar的定义，使其包含child_num和child数组的不变性*)
Definition child_similar (ls1 ls2: list cspace_val_type):=
  forall node,
    child_num_of (nth_cspace (Z.to_nat(Int.unsigned node)) ls1) = child_num_of (nth_cspace (Z.to_nat(Int.unsigned node)) ls2) /\
    children_val_of (nth_cspace (Z.to_nat(Int.unsigned node)) ls1) = children_val_of (nth_cspace (Z.to_nat(Int.unsigned node)) ls2).
Lemma child_similar_trans:
forall ls1 ls2 ls3 ,
  child_similar ls1 ls2 ->
  child_similar ls2 ls3  ->
  child_similar ls1 ls3.
Proof.
  intros. unfold child_similar in *. eauto.
  intro node.
  pose proof H node as H.
  pose proof H0 node as H0.
  destruct H, H0. 
  split. 
  rewrite H. auto. 
  rewrite H1. auto.
Qed.
Lemma child_similar_reflex:
  forall ls1 ls2,
  child_similar ls1 ls2 ->
  child_similar ls2 ls1.
Proof.
  intros.
  unfold child_similar in *.
  intros. 
  lets Hx: H node. 
  destruct Hx. split; auto.
Qed.

Lemma child_similar_nil:
  child_similar nil nil.
Proof.
  unfold child_similar.
  intros.
  rewrite nth_cspace_nil.
  split; auto. 
Qed.

Require Import symbolic_lemmas.
Require Import int_auto.
Open Scope list. 






Lemma children_val_eq_child: 
forall node ls1 ls2 map, 
  child_similar ls1 ls2 ->
  child node ls1 map = child node ls2 map. 
Proof.
   intros. 
   unfold child. 
   unfold child_similar in H. 
   lets Hx: H node. 
   destruct( nth_cspace
   (Z.to_nat (Int.unsigned node)) ls1);
   destruct (nth_cspace
   (Z.to_nat (Int.unsigned node)) ls2).
   destruct c, p, p, p. 
   destruct c0, p, p, p. 
   simpl in Hx. destruct Hx. inverts H0. inverts H1. 
   auto. 
   destruct c, p, p, p. 
   simpl in Hx. destruct Hx. tryfalse. 
   destruct c, p, p, p. 
   simpl in Hx. destruct Hx. tryfalse. 
   auto.
Qed.


(* Most general form of similarity, written in this way to
   enable induction. *)
Lemma wellform_descendents_child_similar':
  forall node descs ls1 map,
    wellform_descendents node descs ls1 map ->
    forall ls2,
    child_similar ls1 ls2 ->
    wellform_descendents node descs ls2 map.
Proof.
  apply (wellform_descendents_mut
    (fun node descs ls1 map
      (pf1: wellform_descendents node descs ls1 map) => forall ls2,
      child_similar ls1 ls2 ->
      wellform_descendents node descs ls2 map)
    (fun nodes descs ls1 map
      (pf2: wellform_descendents_list nodes descs ls1 map) => forall ls2,
      child_similar ls1 ls2 ->
      wellform_descendents_list nodes descs ls2 map)
  ).
  {
    intros.
    apply wellform_descendents_neqnull; auto. 
    lets Hx: H H0.
    eapply children_val_eq_child with(node:=node)(map:=map) in H0.
    rewrite H0 in Hx. auto.  
  }
  {
    intros.
    apply wellform_descendents_list_leaf.  
  }
  {
    intros.
    apply wellform_descendents_list_cons.
    apply H; apply H1.
    apply H0; apply H1.
    apply e.
  }
Qed.

Lemma wellform_descendents_child_similar:
  forall node descs ls1 ls2 map,
    wellform_descendents node descs ls1 map ->
    child_similar ls1 ls2 ->
    wellform_descendents node descs ls2 map.
Proof.
  intros.
  eapply wellform_descendents_child_similar'; eauto.
Qed.

Lemma wellform_descendents_list_child_similar:
  forall nodes descs ls1 ls2 map,
    wellform_descendents_list nodes descs ls1 map ->
    child_similar ls1 ls2 ->
    wellform_descendents_list nodes descs ls2 map.
Proof.
  intros.
  generalize dependent descs.
  induction nodes.
  {
    intros descs H.
    inversion H.
    apply wellform_descendents_list_leaf.
  }
  {
    intros descs H.
    inversion H.
    apply wellform_descendents_list_cons.
    eapply wellform_descendents_child_similar.
    apply H3. apply H0.
    apply IHnodes. apply H4.
    apply H8.
  }
Qed.
(* Next, we show reset_nth_cspace_slot satisfies child_similar
   property. *)


Lemma nat_ltorge:
  forall x n,
  (x < n)%nat \/ (x >= n)%nat. 
Proof.
    intros.
    lia.
Qed.
Lemma nat_eqorneq:
  forall (x y : nat), 
  (x = y)%nat \/ (x <> y)%nat.
Proof.
  intros.
  lia.
Qed.

(*没有做任何的限制*)

Lemma reset_nth_cspace_slot_child_similar:
  forall ls desc class ,
  child_similar ls (reset_nth_cspace_slot desc class ls).
Proof.
  intros. 
  unfold reset_nth_cspace_slot.
  destruct (nth_cspace
  (Z.to_nat (Int.unsigned desc)) ls) eqn: Heq.
  destruct c, p, p, p, c, p. 
  destruct (nth_slots class l0).
  destruct p, p, c, p.  
  destruct (Int.eq i4 ($ CAP_CATEGORY_TYPE)).
  {
    remember ((i1, i2,
    update_nth_list slot_val_type
      class l0
      ($ SLOT_NULL_CAP,
      ($ 0, ($ 0, $ 0, v0))), i0, l, v, i)) as uval. 
    unfold child_similar.
    intros.
    lets Hc1: nat_ltorge (Z.to_nat(Int.unsigned node)) (length ls).
    lets Hc2: nat_ltorge (Z.to_nat(Int.unsigned desc)) (length ls).
    lets Hc3: nat_eqorneq (Z.to_nat(Int.unsigned node)) (Z.to_nat(Int.unsigned desc)).
    destruct Hc1; destruct Hc2; destruct Hc3.
    unfold child. 
    rewrite H1 in *.
    rewrite Heq.
    assert(nth_cspace (Z.to_nat (Int.unsigned desc))
    (update_nth_list cspace_val_type
       (Z.to_nat (Int.unsigned desc)) ls
       uval) = Some uval).
    eapply update_nth_cspace_eq; auto. 
    rewrite H2. subst uval. auto. 
    unfold child. 
    assert( nth_cspace
    (Z.to_nat (Int.unsigned node))
    (update_nth_list cspace_val_type
       (Z.to_nat (Int.unsigned desc))
       ls uval) = nth_cspace
       (Z.to_nat (Int.unsigned node)) ls).
    eapply update_nth_cspace_neqrev; auto.
    rewrite H2. auto.  
    eapply update_nth_cspace_remain with(v:= uval)in H0. 
    
    rewrite H0. auto. 
    eapply update_nth_cspace_remain with(v:= uval)in H0. 
    rewrite H0. auto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
  }
  destruct (Int.eq i4 ($ CAP_OBJECT_TYPE)).
  {
    remember ((i1, i2,
    update_nth_list slot_val_type
      class l0
      ($ SLOT_NULL_CAP,
      ($ 0, ($ 0,i6, Vnull))), i0, l, v, i)) as uval. 
    unfold child_similar.
    intros.
    lets Hc1: nat_ltorge (Z.to_nat(Int.unsigned node)) (length ls).
    lets Hc2: nat_ltorge (Z.to_nat(Int.unsigned desc)) (length ls).
    lets Hc3: nat_eqorneq (Z.to_nat(Int.unsigned node)) (Z.to_nat(Int.unsigned desc)).
    destruct Hc1; destruct Hc2; destruct Hc3.
    unfold child. 
    rewrite H1 in *.
    rewrite Heq.
    assert(nth_cspace (Z.to_nat (Int.unsigned desc))
    (update_nth_list cspace_val_type
       (Z.to_nat (Int.unsigned desc)) ls
       uval) = Some uval).
    eapply update_nth_cspace_eq; auto. 
    rewrite H2. subst uval. auto. 
    unfold child. 
    assert( nth_cspace
    (Z.to_nat (Int.unsigned node))
    (update_nth_list cspace_val_type
       (Z.to_nat (Int.unsigned desc))
       ls uval) = nth_cspace
       (Z.to_nat (Int.unsigned node)) ls).
    eapply update_nth_cspace_neqrev; auto.
    rewrite H2. auto.  
    eapply update_nth_cspace_remain with(v:= uval)in H0. 
    
    rewrite H0. auto. 
    eapply update_nth_cspace_remain with(v:= uval)in H0. 
    rewrite H0. auto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
  }
  {
  remember ((i1, i2,
    update_nth_list slot_val_type
      class l0
      ($ SLOT_NULL_CAP,
      (i4, (i5,i6, v0))), i0, l, v, i)) as uval. 
    unfold child_similar.
    intros.
    lets Hc1: nat_ltorge (Z.to_nat(Int.unsigned node)) (length ls).
    lets Hc2: nat_ltorge (Z.to_nat(Int.unsigned desc)) (length ls).
    lets Hc3: nat_eqorneq (Z.to_nat(Int.unsigned node)) (Z.to_nat(Int.unsigned desc)).
    destruct Hc1; destruct Hc2; destruct Hc3.
    unfold child. 
    rewrite H1 in *.
    rewrite Heq.
    assert(nth_cspace (Z.to_nat (Int.unsigned desc))
    (update_nth_list cspace_val_type
       (Z.to_nat (Int.unsigned desc)) ls
       uval) = Some uval).
    eapply update_nth_cspace_eq; auto. 
    rewrite H2. subst uval. auto. 
    unfold child. 
    assert( nth_cspace
    (Z.to_nat (Int.unsigned node))
    (update_nth_list cspace_val_type
       (Z.to_nat (Int.unsigned desc))
       ls uval) = nth_cspace
       (Z.to_nat (Int.unsigned node)) ls).
    eapply update_nth_cspace_neqrev; auto.
    rewrite H2. auto.  
    eapply update_nth_cspace_remain with(v:= uval)in H0. 
    
    rewrite H0. auto. 
    eapply update_nth_cspace_remain with(v:= uval)in H0. 
    rewrite H0. auto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
  }
  unfold child_similar; intros. auto.
  unfold child_similar; intros. auto.
Qed.

Lemma reset_nth_cspace_slot_option_child_similar:
  forall ls ls1 desc class n_class ,
  reset_nth_cspace_slot_option desc class n_class ls ls1 ->
  child_similar ls ls1.
Proof.
  intros.
  unfold reset_nth_cspace_slot_option in H.
  simpljoin.
  unfolds in H.
  destruct ((0 <=? n_class)%nat &&(n_class <? Z.to_nat SLOT_NUM)%nat).
  subst ls1.
  eapply reset_nth_cspace_slot_child_similar; eauto.
  subst ls1.
  unfold child_similar.
  intros. auto.
Qed.
  
(* This is followed by similar result for reset_nthlist_cspace_slot. *)
Lemma reset_nthlist_cspace_slot_child_similar:
  forall ls descs class,
    child_similar ls (reset_nthlist_cspace_slot descs class ls).
Proof.
  intros.
  generalize dependent ls.
  induction descs.
  {
    intro ls.
    simpl. unfold child_similar. auto.
  }
  {
    intro ls.
    simpl.
    pose proof child_similar_trans ls (reset_nthlist_cspace_slot descs class ls) as H.
    apply H. apply IHdescs.
    apply reset_nth_cspace_slot_child_similar.
  }
Qed.

(* This directly yields similarity results for reset_nth_cspace_slot
   and reset_nthlist_cspace_slot. *)
Lemma reset_nth_cspace_slot_descs_similar:
  forall node descs ls map node2 class,
    wellform_descendents node descs ls map ->
    wellform_descendents node descs (reset_nth_cspace_slot node2 class ls) map.
Proof.
  intros.
  eapply wellform_descendents_child_similar.
  apply H. apply reset_nth_cspace_slot_child_similar.
Qed.

Lemma reset_nthlist_cspace_slot_descs_similar:
  forall node descs ls map node2 class,
    wellform_descendents node descs ls map ->
    wellform_descendents node descs (reset_nthlist_cspace_slot node2 class ls) map.
Proof.
  intros.
  eapply wellform_descendents_child_similar.
  apply H. apply reset_nthlist_cspace_slot_child_similar.
Qed.

Lemma reset_nth_cspace_slot_descs_list_similar:
  forall nodes descs ls map node2 class,
    wellform_descendents_list nodes descs ls map ->
    wellform_descendents_list nodes descs (reset_nth_cspace_slot node2 class ls) map.
Proof.
  intros.
  eapply wellform_descendents_list_child_similar.
  apply H. 
  apply reset_nth_cspace_slot_child_similar.
Qed.

Lemma reset_nthlist_cspace_slot_descs_list_similar:
  forall nodes descs ls map node2 class,
    wellform_descendents_list nodes descs ls map ->
    wellform_descendents_list nodes descs (reset_nthlist_cspace_slot node2 class ls) map.
Proof.
  intros.
  eapply wellform_descendents_list_child_similar.
  apply H. apply reset_nthlist_cspace_slot_child_similar.
Qed.


Lemma reset_nth_cspace_slot_len_eq:
  forall x y vl,
  length (reset_nth_cspace_slot x y vl) = 
  length vl. 
Proof.
  intros x y vl.
  unfold reset_nth_cspace_slot.
  destruct (nth_cspace (Z.to_nat (Int.unsigned x)) vl).
  destruct c; destruct p; destruct p; destruct p;destruct c; destruct p.
  destruct (nth_slots y l0).
  destruct p; destruct p; destruct c; destruct p.
  destruct (Int.eq i4 ($ CAP_CATEGORY_TYPE)).
  rewrite update_nth_list_len_eq. auto.
  destruct (Int.eq i4 ($ CAP_OBJECT_TYPE)).
  rewrite update_nth_list_len_eq. auto.
  rewrite update_nth_list_len_eq. auto.
  auto. auto.
Qed.
  
Lemma reset_nthlist_cspace_slot_len_eq:
  forall l n ls,
  length (reset_nthlist_cspace_slot l n ls) = length ls. 
Proof.
  induction l; intros.
  simpl. auto.
  simpl.
  rewrite reset_nth_cspace_slot_len_eq.
  eapply IHl.
Qed.

(* Relation between reset_nthlist_cspace_slot and append. *)
Lemma reset_nthlist_cspace_slot_append:
  forall desc1 desc2 class ls,
    reset_nthlist_cspace_slot (desc1 ++ desc2) class ls =
    reset_nthlist_cspace_slot desc1 class (
      reset_nthlist_cspace_slot desc2 class ls).
Proof.
  intros.
  induction desc1.
  {
    intros. simpl. auto.
  }
  {
    intros. simpl.
    rewrite IHdesc1. auto.
  }
Qed.

Lemma reset_nth_cspace_neqrev: 
  forall node1 node2  class ls,
  Z.to_nat (Int.unsigned node1) <>
  Z.to_nat (Int.unsigned node2) ->
  nth_cspace(Z.to_nat (Int.unsigned node1))
  (reset_nth_cspace_slot node2 class ls) 
  = nth_cspace(Z.to_nat (Int.unsigned node1)) ls. 
Proof.
  intros.
  lets Hx: nat_ltorge (Z.to_nat (Int.unsigned node1)) (length ls).
  lets Hy: nat_ltorge (Z.to_nat (Int.unsigned node2)) (length ls).
  destruct Hx.
  2:{
    assert(length (reset_nth_cspace_slot node2 class
    ls) = length ls).
    eapply reset_nth_cspace_slot_len_eq.
    assert(Z.to_nat (Int.unsigned node1) >= length(reset_nth_cspace_slot node2 class ls))%nat. 
    rewrite H1. auto. 
    eapply nth_cspace_none in H0.
    eapply nth_cspace_none in H2.
    rewrite H0, H2.
    auto.
  }
  destruct Hy.
  2:{
    unfold reset_nth_cspace_slot.
    eapply nth_cspace_none in H1.
    rewrite H1.
    auto.
  }
  unfold reset_nth_cspace_slot.
  destruct (nth_cspace(Z.to_nat (Int.unsigned node2))ls).
  destruct c, p, p,p, c, p. 
  destruct (nth_slots class l0).
  destruct p,p,c,p.
  destruct (Int.eq i4 ($ CAP_CATEGORY_TYPE)).
  eapply update_nth_cspace_neqrev; eauto. 
  destruct (Int.eq i4 ($ CAP_OBJECT_TYPE)).
  eapply update_nth_cspace_neqrev; eauto.
  eapply update_nth_cspace_neqrev; eauto.
  auto.
  auto.
Qed.

Lemma reset_nth_cspace_slot_remain:
  forall node class ls,
  (Z.to_nat(Int.unsigned node) >= length ls)%nat ->
  reset_nth_cspace_slot node class ls = ls. 
Proof.
  intros.
  unfold reset_nth_cspace_slot.
  eapply nth_cspace_none in H.
  rewrite H.
  auto.
Qed.




Lemma reset_nth_cspace_slot_swap: 
  forall ls node1 node2 class ,
  reset_nth_cspace_slot node1 class (
    reset_nth_cspace_slot node2 class ls
  ) = reset_nth_cspace_slot node2 class(
    reset_nth_cspace_slot node1 class ls
  ).
Proof.
  intros.
  assert(Hlen1: length(reset_nth_cspace_slot node1 class ls) = length ls).
  eapply reset_nth_cspace_slot_len_eq.
  assert(Hlen2: length(reset_nth_cspace_slot node2 class ls) = length ls).
  eapply reset_nth_cspace_slot_len_eq.
  
  assert(Z.to_nat(Int.unsigned node1) = Z.to_nat(Int.unsigned node2) \/
  Z.to_nat(Int.unsigned node1) <> Z.to_nat(Int.unsigned node2)) by lia.
  destruct H.
  Require Import inline_bittblfunctions.
  eapply inline_bittblfunctions.z2n_int_eq in H.
  subst node2. auto.
  {
    lets Hx: nat_ltorge (Z.to_nat (Int.unsigned node1)) (length ls).
    lets Hy: nat_ltorge (Z.to_nat (Int.unsigned node2)) (length ls).
    destruct Hx.
    {
      destruct Hy.
      2:{
        assert((Z.to_nat (Int.unsigned node2) >=
        length ls))%nat by auto.
        rewrite <- Hlen1 in H2.
        eapply reset_nth_cspace_slot_remain with(class:=class) in H1.
        eapply reset_nth_cspace_slot_remain with(class:=class) in H2.
        rewrite H2.
        rewrite H1. auto.
      }
      {
        unfold reset_nth_cspace_slot.
        destruct (nth_cspace(Z.to_nat (Int.unsigned node2)) ls) eqn: Hls2.
        destruct c, p, p, p, c, p.
        destruct (nth_slots class l0) eqn: Hl0.
        destruct p, p, c, p.
        destruct (Int.eq i4 ($ CAP_CATEGORY_TYPE)) eqn: Hi3.
        rewrite update_nth_cspace_neqrev; eauto.
        destruct (nth_cspace (Z.to_nat (Int.unsigned node1))
        ls) eqn: Hls1.
        destruct c, p, p, p, c, p.
        destruct (nth_slots class l2) eqn: Hl2.
        destruct p, p, c, p.
        destruct (Int.eq i12 ($ CAP_CATEGORY_TYPE)) eqn: Hi10.
        rewrite update_nth_cspace_neqrev; eauto.
        rewrite Hls2.
        rewrite Hl0. rewrite Hi3. 
        eapply update_nth_list_swap; eauto.
        destruct(Int.eq i12 ($ CAP_OBJECT_TYPE)) eqn: Hi10o.
        rewrite update_nth_cspace_neqrev; eauto.
        rewrite Hls2. rewrite Hl0.
        rewrite Hi3. eapply update_nth_list_swap; eauto.
        rewrite update_nth_cspace_neqrev; eauto.
        rewrite Hls2. rewrite Hl0. rewrite Hi3.
        eapply update_nth_list_swap; eauto.
        rewrite Hls2. rewrite Hl0. rewrite Hi3. auto.
        rewrite Hls2. rewrite Hl0. rewrite Hi3. auto.
        destruct (Int.eq i4 ($ CAP_OBJECT_TYPE)) eqn: Hi3o.
        rewrite update_nth_cspace_neqrev; eauto.
        destruct (nth_cspace (Z.to_nat (Int.unsigned node1))
        ls) eqn: Hls1.
        destruct c,p,p,p,c,p.
        destruct (nth_slots class l2 ) eqn: Hl2.
        destruct p,p,c,p.
        destruct (Int.eq i12 ($ CAP_CATEGORY_TYPE)) eqn: Hi10.
        rewrite update_nth_cspace_neqrev; eauto.
        rewrite Hls2. rewrite Hl0. rewrite Hi3. rewrite Hi3o. 
        eapply update_nth_list_swap; eauto.
        destruct (Int.eq i12 ($ CAP_OBJECT_TYPE)) eqn: Hi10o.
        rewrite update_nth_cspace_neqrev; eauto.
        rewrite Hls2. rewrite Hl0. rewrite Hi3. rewrite Hi3o. 
        eapply update_nth_list_swap; eauto.
        rewrite update_nth_cspace_neqrev; eauto.
        rewrite Hls2. rewrite Hl0. rewrite Hi3. rewrite Hi3o. 
        eapply update_nth_list_swap; eauto.
        rewrite Hls2. rewrite Hl0. rewrite Hi3. rewrite Hi3o. auto.
        rewrite Hls2. rewrite Hl0. rewrite Hi3. rewrite Hi3o. auto.
        rewrite update_nth_cspace_neqrev; eauto.
        destruct (nth_cspace (Z.to_nat (Int.unsigned node1))
        ls) eqn: Hls1.
        destruct c,p,p,p,c,p. 
        destruct (nth_slots class l2) eqn: Hl2.
        destruct p,p,c,p.
        destruct (Int.eq i12 ($ CAP_CATEGORY_TYPE)) eqn: Hi10.
        rewrite update_nth_cspace_neqrev; eauto.
        rewrite Hls2. rewrite Hl0. rewrite Hi3. rewrite Hi3o. 
        eapply update_nth_list_swap; eauto.
        destruct (Int.eq i12 ($ CAP_OBJECT_TYPE)) eqn: Hi10o.
        rewrite update_nth_cspace_neqrev; eauto.
        rewrite Hls2. rewrite Hl0. rewrite Hi3. rewrite Hi3o. 
        eapply update_nth_list_swap; eauto.
        rewrite update_nth_cspace_neqrev; eauto.
        rewrite Hls2. rewrite Hl0. rewrite Hi3. rewrite Hi3o. 
        eapply update_nth_list_swap; eauto.
        rewrite Hls2. rewrite Hl0. rewrite Hi3. rewrite Hi3o. auto.
        rewrite Hls2. rewrite Hl0. rewrite Hi3. rewrite Hi3o. auto.
        destruct (nth_cspace (Z.to_nat (Int.unsigned node1))
        ls) eqn: Hls1.
        destruct c,p,p,p,c,p. 
        destruct (nth_slots class l2) eqn: Hl2.
        destruct p,p,c,p.
        destruct (Int.eq i8($ CAP_CATEGORY_TYPE)) eqn: Hi6.
        rewrite update_nth_cspace_neqrev; eauto.
        rewrite Hls2. rewrite Hl0. auto.
        destruct (Int.eq i8 ($ CAP_OBJECT_TYPE)) eqn: Hi6o.
        rewrite update_nth_cspace_neqrev; eauto.
        rewrite Hls2. rewrite Hl0. auto.
        rewrite update_nth_cspace_neqrev; eauto.
        rewrite Hls2. rewrite Hl0. auto.
        rewrite Hls2. rewrite Hl0. auto.
        rewrite Hls2. rewrite Hl0. auto.
        destruct ( nth_cspace
        (Z.to_nat (Int.unsigned node1)) ls) eqn: Hls1.
        destruct c,p,p,p,c,p.
        destruct (nth_slots class l0) eqn: Hl0.
        destruct p,p,c,p.
        destruct (Int.eq i4 ($ CAP_CATEGORY_TYPE)) eqn: Hi3.
        rewrite update_nth_cspace_neqrev; eauto.
        rewrite Hls2. auto.
        destruct (Int.eq i4 ($ CAP_OBJECT_TYPE)) eqn: Hi3o.
        rewrite update_nth_cspace_neqrev; eauto.
        rewrite Hls2. auto.
        rewrite update_nth_cspace_neqrev; eauto.
        rewrite Hls2. auto.
        rewrite Hls2. auto.
        rewrite Hls2. auto.
      }
    }
    {
      assert((Z.to_nat (Int.unsigned node1) >=
      length ls))%nat by auto.
      rewrite <- Hlen2 in H1.
      eapply reset_nth_cspace_slot_remain with(class:=class) in H1.
      eapply reset_nth_cspace_slot_remain with(class:=class) in H0.
      rewrite H0.
      rewrite H1. auto.
    }
  
  }
Qed.



Lemma reset_nthlist_cspace_slot_cons2:
  forall node descs class ls,
    contains descs node = false ->
    reset_nth_cspace_slot node class (
      reset_nthlist_cspace_slot descs class ls) =
    reset_nthlist_cspace_slot descs class (
      reset_nth_cspace_slot node class ls).
Proof.
  intros.
  generalize dependent node.
  induction descs.
  {
    simpl. auto.
  }
  {
    intros.
    simpl. rewrite <- IHdescs.
    
    simpl in H. destruct (Int.eq a node). tryfalse. auto.
    eapply reset_nth_cspace_slot_swap.
    simpl in H. 
    destruct (Int.eq a node). tryfalse.
    auto. 
  }
Qed.

Lemma reset_nthlist_cspace_slot_append2:
  forall desc1 desc2 class ls,
    intersection desc1 desc2 = false ->
    reset_nthlist_cspace_slot (desc1 ++ desc2) class ls =
    reset_nthlist_cspace_slot desc2 class (
      reset_nthlist_cspace_slot desc1 class ls).
Proof.
  intros.
  induction desc1.
  {
    simpl. auto.
  }
  {
    simpl. rewrite IHdesc1.
    rewrite reset_nthlist_cspace_slot_cons2.
    auto. simpl in H. 
    eapply orb_false_elim in H. 
    destruct H. auto. 
    simpl in H. 
    eapply orb_false_elim in H. 
    destruct H. auto.
  }
Qed. 

(* The following lemma states that resetting all descendents
   can be computed in two ways: first
*)
(* Lemma reset_descendents_recursive:
  (forall node class map ls ls2,
    reset_descendents_cspace_slot node class map ls ls2 ->
    forall descs,
    wellform_descendents node descs ls map ->
    reset_nthlist_cspace_slot descs class ls = ls2).
Proof.
  apply (reset_descendents_cspace_slot_mut
    (fun node class map ls ls2 
      (pf1: reset_descendents_cspace_slot node class map ls ls2) => forall descs,
      wellform_descendents node descs ls map ->
      reset_nthlist_cspace_slot descs class ls = ls2)
    (fun nodes class map ls ls2
      (pf2: reset_descendents_cspace_list_slot nodes class map ls ls2) => forall descs,
      wellform_descendents_list nodes descs ls map ->
      reset_nthlist_cspace_slot descs class ls = ls2)
  ).
  {
    intros.
    pose proof wellform_descendents_unique node childs descs ls map w H0 as eq_descs.
    rewrite eq_descs in *.
    inversion w.
    simpl.
    assert(child_similar ls ls1).
    rewrite <- e.
    eapply reset_nth_cspace_slot_child_similar.
    lets Hx: wellform_descendents_list_child_similar H1 H7.

    apply H in Hx. clear H.
    rewrite <- Hx.
    rewrite <- e.
    eapply reset_nthlist_cspace_slot_cons2.
    auto.
  }
  {
    intros.
    inversion H.
    simpl. auto.
  }
  {
    intros.
    inversion H1.
    apply H in H4; clear H.
    pose proof reset_nthlist_cspace_slot_descs_list_similar
                 rest desc2 ls map desc1 class H5 as H5'; clear H5.
    rewrite H4 in H5'.
    apply H0 in H5'; clear H0.
    rewrite reset_nthlist_cspace_slot_append2.
    rewrite H4. rewrite H5'. auto.
    eauto.
  }
Qed. *)




Lemma nth_cspace_add1:
  forall idx l x,
    nth_cspace (idx + 1)%nat (x :: l)
    = nth_cspace idx l. 
Proof.
  induction idx; intros.
  simpl. auto.
  simpl.
  destruct l. rewrite nth_cspace_nil. auto.
  eapply IHidx.
Qed.




Lemma reset_descendents_cspace_slot_similar:
  forall node class map ls ls2 ,
  reset_descendents_cspace_slot node class map ls ls2 ->
  child_similar ls ls2.
Proof. 
  apply (reset_descendents_cspace_slot_mut
  (fun node class map ls ls2 
    (pf1: reset_descendents_cspace_slot node class map ls ls2) => (child_similar ls ls2))
  (fun nodes class map ls ls2
    (pf2: reset_descendents_cspace_list_slot nodes class map ls ls2) => (child_similar ls ls2))
  ).
  {
    intros.
    assert(child_similar ls ls1).
    destruct e.
    eapply reset_nth_cspace_slot_option_child_similar; eauto.
    eapply child_similar_trans; eauto.
  }
  {
    unfold child_similar.
    intros.
    split; auto.
  }
  {
    intros.
    lets Hx: child_similar_trans H H0.
    eapply Hx.
  }
Qed.
Lemma reset_descdents_list_nil: 
  forall class map ls ls2,
  reset_descendents_cspace_list_slot nil class map ls ls2 ->
  ls = ls2.
Proof.
  intros.
  inversion H. auto. 
Qed.



Lemma reset_descendents_cspace_list_slot_similar:
  forall nodes class map ls ls2 ,
  reset_descendents_cspace_list_slot nodes class map ls ls2 ->
  child_similar ls ls2.
Proof. 
  induction nodes; intros.
  eapply reset_descdents_list_nil in H. 
  rewrite H. unfold child_similar. intros. auto. 
  inversion H. 
  eapply reset_descendents_cspace_slot_similar in H2. 
  eapply IHnodes in H7. 
  lets Hx: child_similar_trans H2 H7. auto. 
Qed.



Lemma reset_descendents_cspace_slot_length_eq:
  forall node class map ls ls2 ,
  reset_descendents_cspace_slot node class map ls ls2 ->
  (length ls = length ls2)%nat.
Proof.  
  apply (reset_descendents_cspace_slot_mut
  (fun node class map ls ls2 
    (pf1: reset_descendents_cspace_slot node class map ls ls2) => (length ls = length ls2))
  (fun nodes class map ls ls2
    (pf2: reset_descendents_cspace_list_slot nodes class map ls ls2) => (length ls = length ls2))
  ).
  {
    intros. 
    assert(length ls1 = length ls). 
    
    simpljoin.
    unfold reset_nth_cspace_slot_option in H0.
    simpljoin.
    destruct((0 <=? x)%nat &&
    (x <? Z.to_nat SLOT_NUM)%nat).
    subst ls1.
    eapply reset_nth_cspace_slot_len_eq.
    subst ls1.
    auto.
    rewrite <- H0.
    auto.
  }
  {
    intros. 
    auto. 
  }
  {
    intros. 
    rewrite H. auto. 
  }
Qed.

Lemma reset_descendents_cspace_list_slot_length_eq:
  forall nodes class map ls ls2 ,
  reset_descendents_cspace_list_slot nodes class map ls ls2 ->
  (length ls = length ls2)%nat.
Proof. 
  induction nodes; intros.
  eapply reset_descdents_list_nil in H. 
  rewrite H. auto.
  inversion H. 
  eapply IHnodes in H7.
  eapply reset_descendents_cspace_slot_length_eq in H2.
  rewrite H2. rewrite <- H7.
  auto.
Qed.

Lemma reset_descendents_cspace_list_slot_append: 
  forall nodes node class map ls ls1 ls2,
  reset_descendents_cspace_list_slot nodes class map ls ls1 ->
  reset_descendents_cspace_slot node class map ls1 ls2 ->
  reset_descendents_cspace_list_slot (nodes ++ node ::nil) class map ls ls2.
Proof.
  induction nodes; intros. 
  eapply reset_descendents_cspace_list_slot_cons; eauto.
  eapply reset_descdents_list_nil in H. 
  subst ls. eapply H0. 
  eapply reset_descendents_cspace_list_slot_nil.
  simpl.
  inversion H.
  eapply reset_descendents_cspace_list_slot_cons.
  eauto.
  eapply IHnodes; eauto.
Qed.



Definition CNode_delete_recursivePre'(vl:vallist) (logicl:list logicvar) ct:=
  EX cid  func_capType func_capability er s cs isr ptrvl priotbl b i  cspacels index childlist
  b1 i1 semvl b2 i2 mutexvl b3 i3 mqvl pointervl vl' rtbl tcbls ptls vhold,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  [| nth_val 0 vl = Some (Vptr cid) |] **
  [| nth_val 1 vl = Some (Vint32 func_capType) |] **
  [| nth_val 2 vl = Some (Vint32 func_capability) |] **
  [|get cspacels cid = Some index|] **
  [|Int.unsigned index < 64|] ** 
  [|wellform_descendents index childlist priotbl cspacels|] **
  (*用这个来说明当前节点以及后代节点构成的树结构*)
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
  AOSCSpacePrioTbl (b, i) ptrvl priotbl cspacels**
  ASeminfo (b1, i1) semvl ** 
  APthreadMutex(b2, i2) mutexvl **  (*Check_Cap_Type函数所需要的数据结构*)
  AMqAttr (b3, i3) mqvl **
  AOSCSpaceObjectPointer pointervl ** 
  AOSTCBPrioTbl vl' rtbl tcbls ptls vhold **
  [|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er) ::
  (logic_cspacel priotbl) :: (logic_llv semvl) :: (logic_llv mutexvl) :: (logic_llv mqvl)::
  (logic_abscap cspacels) ::(logic_lv ptrvl) ::(logic_val (Vptr(b, i))) :: 
  (logic_lv pointervl) :: (logic_lv vl'):: (logic_lv rtbl) :: (logic_abstcb tcbls) :: (logic_absptb ptls) :: (logic_val (Vptr vhold))::
  (logic_val (Vptr(b1, i1)))::(logic_val (Vptr(b2, i2))):: 
  (logic_val (Vptr(b3, i3)))::(logic_code s)::nil|] **
  p_local OSLInv ct init_lg.

Theorem CNode_delete_recursiveGood (vl:vallist) ll ct:
  GoodFunAsrt (CNode_delete_recursivePre' vl ll ct).
Proof.
    GoodFunAsrt_solver.
Qed.

Definition CNode_delete_recursivePre : fpre :=
  fun vl ll ct => mkfunasrt (CNode_delete_recursiveGood vl ll ct).


Definition CNode_delete_recursivePost'(vl:vallist) (logicl:list logicvar) ct:=
    EX cid func_capType func_capability  er s cs isr ptrvl priotbl priotbl' b i cspacels index
    b1 i1 semvl b2 i2 mutexvl b3 i3 mqvl pointervl vl' rtbl tcbls ptls vhold,
    Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
    <|| s ||> **
    [|get cspacels cid = Some index|] **
    [| nth_val 0 vl = Some (Vptr cid) |] **
    [| nth_val 1 vl = Some (Vint32 func_capType) |] **
    [| nth_val 2 vl = Some (Vint32 func_capability) |] **
    [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
    [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
    AOSCSpacePrioTbl (b, i) ptrvl priotbl' cspacels**
    ASeminfo (b1, i1) semvl ** 
    APthreadMutex(b2, i2) mutexvl ** 
    AMqAttr (b3, i3) mqvl **
    AOSCSpaceObjectPointer pointervl ** 
    AOSTCBPrioTbl vl' rtbl tcbls ptls vhold **
    [|reset_descendents_cspace_slot index (Z.to_nat(Int.unsigned func_capability)) cspacels priotbl priotbl'|] **
    [|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er)::
    (logic_cspacel priotbl) :: (logic_llv semvl) :: (logic_llv mutexvl) :: (logic_llv mqvl) ::
    (logic_abscap cspacels) ::(logic_lv ptrvl) :: (logic_val (Vptr(b, i))) ::
    (logic_lv pointervl) :: (logic_lv vl'):: (logic_lv rtbl) :: (logic_abstcb tcbls) :: (logic_absptb ptls) :: (logic_val (Vptr vhold))::
    (logic_val (Vptr(b1, i1))):: (logic_val (Vptr(b2, i2)))::
    (logic_val (Vptr(b3, i3))) :: (logic_code s)::nil|] **
    p_local OSLInv ct init_lg.
Theorem CNode_delete_recursivePostGood (vl:vallist) ll ct:
    GoodFunAsrt (CNode_delete_recursivePost' vl ll ct).
Proof.
    GoodFunAsrt_solver.
Qed.

Definition CNode_delete_recursivePost : fpost :=
  fun vl v ll ct => mkfunasrt (CNode_delete_recursivePostGood vl ll ct).
Definition CNode_delete_recursive_spec : fspec :=
  (CNode_delete_recursivePre,CNode_delete_recursivePost,(Tvoid, Tptr CSPACE::Tint8::Tint32::nil)).


(*ucos_cnode_revoke*)
Definition ucos_CNode_RevokePre'(vl:vallist) (logicl:list logicvar) ct:=
  EX destTask_Prio func_capType func_capability er s cs isr ptrvl priotbl b i  cspacels childlist
  b1 i1 semvl b2 i2 mutexvl b3 i3 mqvl pointervl vl' rtbl tcbls ptls vhold,
  Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
  <|| s ||> **
  [| nth_val 0 vl = Some (Vint32 destTask_Prio) |] **
  [| nth_val 1 vl = Some (Vint32 func_capType) |] **
  [| nth_val 2 vl = Some (Vint32 func_capability) |] **
  [|wellform_descendents destTask_Prio childlist priotbl cspacels|] **
  (*用这个来说明当前节点以及后代节点构成的树结构*)
  [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
  [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
  AOSCSpacePrioTbl (b, i) ptrvl priotbl cspacels**
  ASeminfo (b1, i1) semvl ** 
  APthreadMutex(b2, i2) mutexvl ** 
  AMqAttr (b3, i3) mqvl **
  AOSCSpaceObjectPointer pointervl ** 
  AOSTCBPrioTbl vl' rtbl tcbls ptls vhold **
  [|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er)::
  (logic_cspacel priotbl) :: (logic_llv semvl) :: (logic_llv mutexvl) :: (logic_llv mqvl) ::
  (logic_abscap cspacels) ::(logic_lv ptrvl) :: (logic_val (Vptr(b, i))) ::
  (logic_lv pointervl) :: (logic_lv vl'):: (logic_lv rtbl) :: (logic_abstcb tcbls) :: (logic_absptb ptls) :: (logic_val (Vptr vhold))::
  (logic_val (Vptr(b1, i1))):: (logic_val (Vptr(b2, i2)))::
  (logic_val (Vptr(b3, i3))) :: (logic_code s)::nil|] **
  p_local OSLInv ct init_lg.

Theorem ucos_CNode_RevokeGood (vl:vallist) ll ct:
  GoodFunAsrt (ucos_CNode_RevokePre' vl ll ct).
Proof.
    GoodFunAsrt_solver.
Qed.

Definition ucos_CNode_RevokePre : fpre :=
  fun vl ll ct => mkfunasrt (ucos_CNode_RevokeGood vl ll ct).

Definition ucos_CNode_RevokePost'(vl:vallist)(v: option val) (logicl:list logicvar) ct:=
    EX destTask_Prio func_capType func_capability er s cs isr ptrvl priotbl priotbl' b i cspacels pCSpace
    b1 i1 semvl b2 i2 mutexvl b3 i3 mqvl pointervl vl' rtbl tcbls ptls vhold,
    Aie false ** Ais nil ** Acs cs ** Aisr isr ** Aier er **
    <|| s ||> **
    [| nth_val 0 vl = Some (Vint32 destTask_Prio) |] **
    [| nth_val 1 vl = Some (Vint32 func_capType) |] **
    [| nth_val 2 vl = Some (Vint32 func_capability) |] **
    [|CSPACEList_P ptrvl 0%nat  cspacels|] **   (*建立映射关系*)
    [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] ** (*映射和列表之间的双向联系*)
    AOSCSpacePrioTbl (b, i) ptrvl priotbl' cspacels**
    ASeminfo (b1, i1) semvl ** 
    APthreadMutex(b2, i2) mutexvl ** 
    AMqAttr (b3, i3) mqvl **
    AOSCSpaceObjectPointer pointervl ** 
    AOSTCBPrioTbl vl' rtbl tcbls ptls vhold **
    [|logicl =(logic_cs cs) :: (logic_isr isr) :: (logic_ier er)::
    (logic_cspacel priotbl) :: (logic_llv semvl) :: (logic_llv mutexvl) :: (logic_llv mqvl) ::
    (logic_abscap cspacels) ::(logic_lv ptrvl) :: (logic_val (Vptr(b, i))) ::
    (logic_lv pointervl) :: (logic_lv vl'):: (logic_lv rtbl) :: (logic_abstcb tcbls) :: (logic_absptb ptls) :: (logic_val (Vptr vhold))::
    (logic_val (Vptr(b1, i1))):: (logic_val (Vptr(b2, i2)))::
    (logic_val (Vptr(b3, i3))) :: (logic_code s)::nil|] **
    p_local OSLInv ct init_lg ** 
    ( ([|Int.unsigned destTask_Prio >= 64|] ** [|v = Some(Vint32 ($ OS_PRIO_INVALID))|] **
    [|priotbl' = priotbl|]) \\//
    ( [|Int.unsigned destTask_Prio < 64|] **
    [|pCSpace = nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl|] **
    (([|pCSpace <> Vnull|] ** [|reset_descendents_cspace_slot destTask_Prio (Z.to_nat (Int.unsigned func_capability)) cspacels priotbl priotbl'|]
    ** [|v = Some(Vint32 ($ CNODE_NONE_FAULT))|])
    \\//( [|pCSpace = Vnull|] ** 
    [|priotbl' = priotbl|] **
    [|v = Some(Vint32($ OS_PRIO_INVALID))|])))). 
Theorem ucos_CNode_RevokePostGood (vl:vallist) v ll ct:
    GoodFunAsrt (ucos_CNode_RevokePost' vl v ll ct).
Proof.
    GoodFunAsrt_solver.
Qed.

Definition ucos_CNode_RevokePost : fpost :=
  fun vl v ll ct => mkfunasrt (ucos_CNode_RevokePostGood vl v ll ct).
Definition ucos_CNode_Revoke_spec : fspec :=
  (ucos_CNode_RevokePre,ucos_CNode_RevokePost,(Int8u, Tint8::Tint8::Tint32::nil)).

Definition oscap_spec_list := 
  (* (OS_EventSearch, OS_EventSearch_spec) :: *)
  (ucos_Grant_Cap, ucos_Grant_Cap_spec) ::
  (ucos_CNode_Mutate, ucos_CNode_Mutate_spec) ::
  (ucos_CNode_Mint, ucos_CNode_Mint_spec) ::
  (ucos_CNode_Copy, ucos_CNode_Copy_spec) ::
  (ucos_CNode_Move, ucos_CNode_Move_spec) ::
  (ucos_CNode_Delete, ucos_CNode_Delete_spec) ::
  (Get_Obj_Slot, Get_Obj_Slot_spec) :: 
  (CNode_delete_recursive, CNode_delete_recursive_spec)::
  (Check_Cap_Type, Check_Cap_Type_spec_weak) ::(*这里使用弱的后件，方便之后的证明*)
  (ucos_CNode_Revoke, ucos_CNode_Revoke_spec) ::
  nil.

Fixpoint convert_spec  (ls : list (fid * fspec)) : fid -> option fspec :=
   match ls with
   | nil => fun _ => None
   | (id,spec) :: ls' => 
     fun (id' : fid) =>  
       if Zeq_bool id id' then 
         Some spec else convert_spec ls' id'
   end.
Definition Cap_spec := convert_spec oscap_spec_list.


Require Import ios_int2.
Require Export os_ucos_h2.
Open Scope code_scope.

Definition IntCall_impl := 
Void ·IntCall·(⌞y@Int8u ⌟)··{
  ⌞ ⌟;
  If  ( y′ ==ₑ ′0 ) { f0(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­) };ₛ
  If  ( y′ ==ₑ ′1 ) { f1(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­) };ₛ
  If  ( y′ ==ₑ ′2 ) { f2(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­) };ₛ
  If  ( y′ ==ₑ ′3 ) { f3(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­) };ₛ
  If  ( y′ ==ₑ ′4 ) { f4(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­) };ₛ
  If  ( y′ ==ₑ ′5 ) { f5(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­) };ₛ
  If  ( y′ ==ₑ ′6 ) { f6(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­) };ₛ
  If  ( y′ ==ₑ ′7 ) { f7(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­) };ₛ
  If  ( y′ ==ₑ ′8 ) { f8(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­) };ₛ
  If  ( y′ ==ₑ ′9 ) { f9(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­) };ₛ
  RETURN
 }·.

 Notation "@IntHandlerCall" := (
  If  ( IntNumCurrent′ ==ₑ ′INT_NUM_MIN )       
  { 
    (* f0(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­)  *)
    EOI(5)
  };ₛ
  If  ( IntNumCurrent′ ==ₑ ′INT_NUM_MIN +ₑ ′1 ) 
  { 
    (* f1(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­)  *)
    EOI(6)
  };ₛ
  If  ( IntNumCurrent′ ==ₑ ′INT_NUM_MIN +ₑ ′2 ) 
  { 
  (* f2(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­)  *)
    EOI(7)
  };ₛ
  If  ( IntNumCurrent′ ==ₑ ′INT_NUM_MIN +ₑ ′3 ) 
  { 
    (* f3(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­)  *)
    EOI(8)
  };ₛ
  If  ( IntNumCurrent′ ==ₑ ′INT_NUM_MIN +ₑ ′4 ) 
  { 
    (* f4(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­)  *)
    EOI(9)
  };ₛ
  If  ( IntNumCurrent′ ==ₑ ′INT_NUM_MIN +ₑ ′5 ) 
  { 
    (* f5(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­)  *)
    EOI(10)
  };ₛ
  If  ( IntNumCurrent′ ==ₑ ′INT_NUM_MIN +ₑ ′6 ) 
  { 
    (* f6(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­)  *)
    EOI(11)
  };ₛ
  If  ( IntNumCurrent′ ==ₑ ′INT_NUM_MIN +ₑ ′7 ) 
  { 
    (* f7(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­)  *)
    EOI(12)
  };ₛ
  If  ( IntNumCurrent′ ==ₑ ′INT_NUM_MIN +ₑ ′8)  
  { 
    (* f8(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­)  *)
    EOI(13)
  };ₛ
  If  ( IntNumCurrent′ ==ₑ ′INT_NUM_MIN +ₑ ′9 ) 
  { 
    (* f9(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­)  *)
    EOI(14)
  };ₛ
  If  ( IntNumCurrent′ ==ₑ ′INT_NUM_MIN +ₑ ′10) 
  { 
    (* f10(­IntHandlerParam′[IntNumCurrent′ − ′INT_NUM_MIN]­)  *)
    EOI(15)
  }
  ).

Definition OSIntEnter_impl :=
Void ·OSIntEnter·(⌞ ⌟)··{
  ⌞  ⌟;
  If(OSRunning′ ==ₑ CTrue){
    If(OSIntNesting′  <ₑ ′255){
         ++OSIntNesting′
    }
   };ₛ
  RETURN
}·.

Definition OSIntExit_impl :=
Void ·OSIntExit·(⌞ ⌟)··{
  ⌞x @ Int32⌟;
  If(OSRunning′ ==ₑ CTrue){
    ENTER_CRITICAL;ₛ
    If(OSIntNesting′  >ₑ ′0){
      −−OSIntNesting′
    };ₛ
    x <- CHECKIS;ₛ
    If((OSIntNesting′==ₑ′0)&&ₑ(OSLockNesting′==ₑ′0)&&ₑ(x′ ==ₑ ′1)){ 
        OSIntExitY′ =ₑ OSUnMapTbl′ [OSRdyGrp′];ₛ
        OSPrioHighRdy′ =ₑ (OSIntExitY′ ≪ ′3) +ₑ OSUnMapTbl′[OSRdyTbl′[OSIntExitY′]];ₛ
        OSPrioCur′ =ₑ OSTCBCur′→OSTCBPrio;ₛ 
        If(OSPrioHighRdy′ !=ₑ OSPrioCur′){
            OSTCBHighRdy′ =ₑ OSTCBPrioTbl′[OSPrioHighRdy′];ₛ
            ++OSCtxSwCtr′;ₛ
            SWITCH
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN
    };ₛ
    EXIT_CRITICAL;ₛ
    RETURN
  }
}·.

Definition OSUserISR_impl :=
(* Void ·OSUserISR·(⌞ ⌟)··{ *)
  OSUserISR ↝ {
    (* ⌞y @ Int32 ⌟; *)
    
    (* DSP_C6x_Save(­);ₛ *)
    OSIntEnter(­);ₛ
    If(OSIntNesting′==ₑ′1){
       (*y′ =ᶠ DSP_C6x_GetCurrentSP(·);ₛ
       OSTCBCur′→ OSTCBStkPtr =ₑ〈OS_STK ∗〉y′*)
       (* OSTCBCur′→ OSTCBStkPtr =ᶠ DSP_C6x_GetCurrentSP(·) *)
       OSIntNesting′=ₑ′1
    };ₛ 
    If(IntNumCurrent′ ≥ ′INT_NUM_MIN &&ₑ IntNumCurrent′ <ₑ ′INT_NUM_MAX
          &&ₑ IntHandler′[IntNumCurrent′ − ′INT_NUM_MIN] !=ₑ ′0){
      (*y′ =ₑ IntNumCurrent′ − ′INT_NUM_MIN;ₛ
      IntCall(­y′­)*)
      fnull(­)
    };ₛ 
    EOINT(IntNumCurrent);ₛ    
    OSIntExit(­);ₛ
    (* DSP_C6x_Resume(­);ₛ *)
    IRET
(*}·.*)
  }.

Definition OSIpc_impl :=
Void ·OSIpc·(⌞ ⌟)··{
    ⌞  ⌟;
    RETURN
}·.

Definition OSIpcISR_impl :=
(* Void ·OSIpcISR·(⌞ ⌟)··{ *)
  OSIpcISR ↝ {
    (* ⌞y @ Int32 ⌟; *)
    
    (* DSP_C6X_SAVE;ₛ *)
    OSIntEnter(­);ₛ
    If(OSIntNesting′==ₑ′1){
      (*y <- GETCURRENTSP ;ₛ
      OSTCBCur′→ OSTCBStkPtr =ₑ〈OS_STK ∗〉′y*)
      (* OSTCBCur′ → OSTCBStkPtr =ᶠ DSP_C6x_GetCurrentSP(·) *)
      OSIntNesting′=ₑ′1
    };ₛ
    OSIpc(­);ₛ
    EOI(6);ₛ
    OSIntExit(­);ₛ
    (* DSP_C6X_RESUME *)
    IRET
(*}·.*)
  }.

Definition OSDispatchISR_impl :=
(* Void ·OSDispatchISR·(⌞ ⌟)··{ *)
  OSDispatchISR ↝ {
    (* ⌞ y @ Int32 ⌟; *)

    (* DSP_C6X_SAVE;ₛ *)
    OSIntEnter(­);ₛ
    If(OSIntNesting′==ₑ′1){
      (*y <- GETCURRENTSP ;ₛ
      OSTCBCur′→ OSTCBStkPtr =ₑ〈OS_STK ∗〉′y;ₛ*)
      (* OSTCBCur′ → OSTCBStkPtr =ᶠ DSP_C6x_GetCurrentSP(·);ₛ
      OSSETSP(〈Int16u〉 OSIsrStk′ +ₑ ′os_isrstk_size − ′4) *)
      OSIntNesting′=ₑ′1
    };ₛ
    If(IntNumCurrent′ ≥ ′INT_NUM_MIN &&ₑ IntNumCurrent′ <ₑ ′INT_NUM_MAX
    &&ₑ IntHandler′[IntNumCurrent′ − ′INT_NUM_MIN] !=ₑ ′0){
      fnull(­)
    };ₛ 
    EOINT(IntNumCurrent);ₛ  
    OSIntExit(­);ₛ
    (* If(OSIntNesting′==ₑ′0){
      OSSETSP(〈Int16u〉 OSTCBCur′→ OSTCBStkPtr)
    };ₛ *)
    (* DSP_C6X_RESUME *)
    IRET
(*}·.*)
  }.

Close Scope code_scope.
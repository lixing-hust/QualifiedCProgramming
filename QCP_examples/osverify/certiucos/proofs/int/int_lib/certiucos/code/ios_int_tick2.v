Require Import ios_int2.
Require Export os_ucos_h2.

Open Scope code_scope.

(*Definition OSTimeTick_impl :=
Void ·OSTimeTick·(⌞ ⌟)··{
  ⌞ ⌟;
  RETURN
}·.*)

Definition OSTickISR_impl :=
(* Void ·OSTickISR·(⌞ ⌟)··{ *)
  OSTickISR ↝ {
    (* ⌞y @ Int32  ⌟; *)
    
    (*DSP_C6x_Save(­);ₛ*)
    OSIntEnter(­);ₛ
    If(OSIntNesting′==ₑ′1){
       (*y′ =ᶠ DSP_C6x_GetCurrentSP(·);ₛ
       OSTCBCur′→ OSTCBStkPtr =ₑ〈OS_STK ∗〉y′*)
       (*OSTCBCur′→ OSTCBStkPtr =ᶠ DSP_C6x_GetCurrentSP(·)*)
       OSIntNesting′=ₑ′1
    };ₛ 
    EOI(4);ₛ
    OSTimeTick(­);ₛ
    OSIntExit(­);ₛ
    (*DSP_C6x_Resume(­);ₛ*)
    IRET
(*}·.*)
  }.

Definition int_unstall_handler_6678_impl :=
Int32 ·int_unstall_handler_6678·(⌞ vecnum @ Int32 ⌟)··{
  ⌞  ⌟;
  If(vecnum′ <ₑ ′INT_NUM_MIN ||ₑ vecnum′ >ₑ ′INT_NUM_MAX){
    RETURN ′ENIVAL(*返回ENIVAL(定义为22)，表示安装中断失败*)
	};ₛ 
  ENTER_CRITICAL;ₛ
  IntHandler′[vecnum′ − ′INT_NUM_MIN] =ₑ ′0;ₛ
  EXIT_CRITICAL;ₛ
  RETURN ′0
}·.

Definition int_unstall_handler_6713_impl :=
Int32 ·int_unstall_handler_6713·(⌞ vecnum @ Int32 ⌟)··{
  ⌞  ⌟;
  If(vecnum′ <ₑ ′INT_NUM_MIN ||ₑ vecnum′ >ₑ ′INT_NUM_MAX){
    RETURN ′ENIVAL(*返回ENIVAL(定义为22)，表示安装中断失败L*)
	};ₛ 
  ENTER_CRITICAL;ₛ
  IntHandler′[vecnum′ − ′INT_NUM_MIN] =ₑ ′0;ₛ
  (*IER′ =ₑ IER′ &ₑ ∼(′1 ≪ vecnum′);ₛ -> int_disable_pic*)
  DINTP (vecnum);ₛ
  EXIT_CRITICAL;ₛ
  RETURN ′0
}·.

Definition Interrupt_Init_impl :=
Void ·Interrupt_Init·(⌞ eventID@Int32; IntNum@Int32⌟)··{
  ⌞ intmux@Int32; y@Int32 ⌟;
  intmux′ =ₑ IntNum′ ÷ ′4;ₛ
  If(intmux′ ==ₑ′1){
    y′ =ₑ (IntNum′ − (intmux′) × ′4) × ′8;ₛ
    CGEM_regs_INTMUX1′ =ₑ (CGEM_regs_INTMUX1′ &ₑ ∼(′255 ≪ y′) |ₑ (eventID′ ≪ y′));ₛ
    (*IER′ =ₑ IER′ |ₑ (′1 ≪ IntNum′);ₛ -> int_enable_pic*)
    RINTP (IntNum);ₛ
    RETURN 
	};ₛ
  If(intmux′ ==ₑ′2){
    y′ =ₑ (IntNum′ − (intmux′) × ′4) × ′8;ₛ
    CGEM_regs_INTMUX2′ =ₑ (CGEM_regs_INTMUX2′ &ₑ ∼(′255 ≪ y′) |ₑ (eventID′ ≪ y′));ₛ
    (*IER′ =ₑ IER′ |ₑ (′1 ≪ IntNum′);ₛ -> int_enable_pic*)
    RINTP (IntNum);ₛ
    RETURN 
	};ₛ
  If(intmux′ ==ₑ′3){
    y′ =ₑ (IntNum′ − (intmux′) × ′4) × ′8;ₛ
    CGEM_regs_INTMUX3′ =ₑ (CGEM_regs_INTMUX3′ &ₑ ∼(′255 ≪ y′) |ₑ (eventID′ ≪ y′));ₛ
    (*IER′ =ₑ IER′ |ₑ (′1 ≪ IntNum′);ₛ -> int_enable_pic*)
    RINTP (IntNum);ₛ
    RETURN 
	};ₛ 
  RETURN
}·.

Definition UserAddrCheck_6678_impl :=
Int8s ·UserAddrCheck_6678·(⌞ addr@Int32u ⌟)··{
  ⌞  ⌟;
  If(′UserAddrStart_6678 ≥ addr′ ||ₑ addr′ >ₑ ′UserAddrEnd){
    RETURN ′0
	};ₛ
  RETURN ′1
}·.

Definition UserAddrCheck_6713_impl :=
Int8s ·UserAddrCheck_6713·(⌞ addr@Int32u ⌟)··{
  ⌞  ⌟;
  If(′UserAddrStart_6713 ≥ addr′ ||ₑ addr′ >ₑ ′UserAddrEnd){
    RETURN ′0
	};ₛ
  RETURN ′1
}·.

Definition int_install_handler_6678_impl :=
Int32 ·int_install_handler_6678·(⌞ vecnum@Int32; prio@Int32; handler@ Int32; param@ (Ptr Void); eventID@Int32⌟)··{
  ⌞ y@Int32 ⌟; 
  If(eventID′ ==ₑ ′CSL_GEM_IPC_LOCAL ||ₑ eventID′ ==ₑ ′CSL_GEM_TINTLN){
    RETURN ′ENIVAL
	};ₛ
  If(vecnum′ <ₑ ′INT_NUM_MIN ||ₑ vecnum′ >ₑ ′INT_NUM_MAX){
    RETURN ′ENIVAL
	};ₛ 
  (*y′ =ₑ 〈Int32〉 handler′;ₛ
  y′ =ᶠ UserAddrCheck_6678(· y′ ·);ₛ*)
  If(′0 ≥ handler′){
    RETURN ′ENIVAL
	};ₛ 
  ENTER_CRITICAL;ₛ 
  (*Interrupt_Init(-eventID′, vecnum′ -);ₛ*)
  IntHandler′[vecnum′ − ′INT_NUM_MIN] =ₑ ′1;ₛ
  (*IntHandlerParam′[vecnum′ − ′INT_NUM_MIN] =ₑ param′;ₛ*)
  RINTP (vecnum);ₛ
  EXIT_CRITICAL;ₛ
  RETURN ′0
}·.

Definition int_install_handler_6713_impl :=
Int32 ·int_install_handler_6713·(⌞ vecnum@Int32; prio@Int32; handler@Int32; param@(Ptr Void) ; eventID@Int32 ⌟)··{
  ⌞ y@Int32 ⌟;
  If(vecnum′ <ₑ ′INT_NUM_MIN ||ₑ vecnum′ >ₑ ′INT_NUM_MAX){
    RETURN ′ENIVAL
	};ₛ 
  (*y′ =ᶠ UserAddrCheck_6713(· handler′ ·);ₛ*)
  If(′0 ≥ handler′){
    RETURN ′ENIVAL
	};ₛ 
  ENTER_CRITICAL;ₛ
  IntHandler′[vecnum′ − ′INT_NUM_MIN] =ₑ ′1;ₛ
  (*IntHandlerParam′[vecnum′ − ′INT_NUM_MIN] =ₑ param′;ₛ*)
  IF (vecnum′ <ₑ ′10){
    IF ((vecnum′ − ′4) >ₑ ′2){
      y′ =ₑ (vecnum′ − ′4)× ′5 +ₑ ′1
    }ELSE{
      y′ =ₑ (vecnum′ − ′4)× ′5
    };ₛ
    INT_MUX_L′ =ₑ (INT_MUX_L′ &ₑ ∼(′31 ≪ y′));ₛ
    INT_MUX_L′ =ₑ (INT_MUX_L′ |ₑ (eventID′ ≪ y′))
  }ELSE{
    IF ((vecnum′ − ′10) >ₑ ′2){
      y′ =ₑ (vecnum′ − ′10)× ′5 +ₑ ′1
    }ELSE{
      y′ =ₑ (vecnum′ − ′10)× ′5
    };ₛ
    INT_MUX_H′ =ₑ (INT_MUX_L′ &ₑ ∼(′31 ≪ y′));ₛ
    INT_MUX_H′ =ₑ (INT_MUX_L′ |ₑ (eventID′ ≪ y′))
  };ₛ
  (*ICR′ =ₑ IFR′ |ₑ ′1 ≪ vecnum′;ₛ*)
	(*IER′ =ₑ IER′ |ₑ ′1 ≪ vecnum′;ₛ -> int_enable_pic*)
  RINTP (vecnum);ₛ
  EXIT_CRITICAL;ₛ
  RETURN ′0
}·.

Definition exception_handler_set_impl :=
Int32 ·exception_handler_set·(⌞ handler@Int32 ⌟)··{
  ⌞ old_handler@Int32 ⌟;
  ENTER_CRITICAL;ₛ
  old_handler′ =ₑ exception_handler′;ₛ
  exception_handler′ =ₑ handler′;ₛ
  EXIT_CRITICAL;ₛ
  RETURN old_handler′
}·.

Close Scope code_scope.
Require Export include_frm2.
Require Export os_code_defs2.
Require Export os_ucos_h2.
Require Export os_cpu_a2.

Open Scope code_scope.

(* constants *)
Definition INT_NUM_MIN  := 5%Z.
Definition INT_NUM_MAX  := 15%Z.
Definition INT_NUM  := 11%Z.
Definition ENIVAL := 30%Z.

Definition UserAddrStart_6678 := 8388608%Z.
Definition UserAddrStart_6713 := 0%Z.
Definition UserAddrEnd := 4294967295%Z.

Definition CSL_GEM_IPC_LOCAL := 1031%Z.
Definition CSL_GEM_TINTLN := 1032%Z.

(* global variables *)
(*xjl将这里的OSTCBStkPtr移到了os_ucos_h.v文件中*)
Definition OSIsrStk : ident := 27102%Z.
Definition OSIsrStkNUM : ident := 27103%Z.
Definition os_isrstk_size : ident := 27104%Z.
Definition IntNumCurrent : ident  := 27105%Z.
Definition IntHandler :ident := 27106%Z.
Definition IntHandlerParam: ident := 27107%Z.
Definition exception_handler : ident := 27108%Z.
Definition IER : ident := 27109%Z.
Definition ICR : ident := 27110%Z.
Definition IFR : ident := 27111%Z.
Definition CGEM_regs_INTMUX1 : ident := 27112%Z.
Definition CGEM_regs_INTMUX2 : ident := 27113%Z.
Definition CGEM_regs_INTMUX3 : ident := 27114%Z.
Definition INT_MUX_L : ident := 27114%Z.
Definition INT_MUX_H : ident := 27115%Z.

(* function identifiers *)
Definition OSIntCtxSw  := 27300%Z.
Definition OS_ENTER_CRITICAL  := 27301%Z.
Definition OS_EXIT_CRITICAL  := 27302%Z.
Definition OSIntEnter  := 27303%Z.
Definition OSIntExit  := 27304%Z.
Definition OSDispatchISR  := 2.
Definition OSUserISR := 3.
Definition OSIpcISR  := 6.
Definition OSTickISR := 4.
Definition user_nmi_ISR := 1.
Definition int_lock := 27310%Z.
Definition int_unlock := 27311%Z.
Definition int_enable_pic := 27312%Z.
Definition int_disable_pic := 27313%Z.

Definition int_install_handler_6678 := 27314%Z.
Definition int_install_handler_6713 := 27315%Z.
Definition int_unstall_handler_6678 := 27316%Z.
Definition int_unstall_handler_6713 := 27317%Z.
Definition exception_handler_set := 27318%Z.

Definition UserAddrCheck_6678 := 27319%Z.
Definition UserAddrCheck_6713 := 27320%Z.
Definition Interrupt_Init := 27321%Z.

Definition f0  := 27322%Z.
Definition f1  := 27323%Z.
Definition f2  := 27324%Z.
Definition f3  := 27325%Z.
Definition f4  := 27326%Z.
Definition f5  := 27327%Z.
Definition f6  := 27328%Z.
Definition f7  := 27329%Z.
Definition f8  := 27330%Z.
Definition f9  := 27331%Z.
Definition f10 := 27332%Z.
Definition fnull := 27333%Z.

Definition OSIpc  := 27396%Z.
(*Definition OSTimeTick   := 27395%Z.*)
Definition OSTimeTick := 74%Z.
Definition OSTaskSuspend := 281%Z.
Definition EXC_HANDLER := 27393%Z.
Definition IntCall := 27392%Z.

(* local variables *)
Definition y : ident := 27500%Z.
Definition level : ident := 27501%Z.
Definition irqLine: ident := 27502%Z.
Definition vecnum : ident  := 27503%Z.
Definition eventID : ident := 27504%Z.
Definition IntNum : ident := 27505%Z.
Definition intmux : ident := 27506%Z. 
Definition addr : ident := 27507%Z.
Definition handler : ident := 27508%Z.
Definition param : ident := 28509%Z.
Definition prio : ident := 27510%Z.
Definition old_handler : ident := 27511%Z.

Definition gvarlistint :decllist := 
            ⌞ 
             IntNumCurrent @ Int8u;
             OSLockNesting @ Int8u;
             IntHandler @ (Tarray (Int32)∘(INT_NUM));
             IntHandlerParam @ (Tarray (Void ∗)∘(INT_NUM));
             os_isrstk_size @ Int16u;
             OSIsrStk @ (Tarray (OS_STK)∘OSIsrStkNUM);
             exception_handler @ Int32;
             CGEM_regs_INTMUX1 @ Int32;
             CGEM_regs_INTMUX2 @ Int32;
             CGEM_regs_INTMUX3 @ Int32;
             INT_MUX_L @ Int32;
             INT_MUX_H @ Int32
            ⌟.   

Definition f0_impl :=
Void ·f0·(⌞⌟)··{
  ⌞ ⌟;
  RETURN
}·.
Definition f1_impl :=
Void ·f1·(⌞⌟)··{
  ⌞ ⌟;
  RETURN
}·.
Definition f2_impl :=
Void ·f2·(⌞⌟)··{
  ⌞ ⌟;
  RETURN
}·.
Definition f3_impl :=
Void ·f3·(⌞⌟)··{
  ⌞ ⌟;
  RETURN
}·.
Definition f4_impl :=
Void ·f4·(⌞⌟)··{
  ⌞ ⌟;
  RETURN
}·.
Definition f5_impl :=
Void ·f5·(⌞⌟)··{
  ⌞ ⌟;
  RETURN
}·.
Definition f6_impl :=
Void ·f6·(⌞⌟)··{
  ⌞ ⌟;
  RETURN
}·.
Definition f7_impl :=
Void ·f7·(⌞⌟)··{
  ⌞ ⌟;
  RETURN
}·.
Definition f8_impl :=
Void ·f8·(⌞⌟)··{
  ⌞ ⌟;
  RETURN
}·.
Definition f9_impl :=
Void ·f9·(⌞⌟)··{
  ⌞ ⌟;
  RETURN
}·.
Definition fnull_impl :=
Void ·fnull·(⌞⌟)··{
  ⌞ ⌟;
  RETURN
}·.                
Definition f10_impl := fnull_impl.

(*
Definition OSIntCtxSw_impl :=
Void ·OSIntCtxSw·(⌞ ⌟)··{
  ⌞ ⌟;
  SWITCH
}·.

Definition OS_ENTER_CRITICAL_impl :=
Void ·OS_ENTER_CRITICAL·(⌞ ⌟)··{
  ⌞ ⌟;
  ENTER_CRITICAL
}·.

Definition OS_EXIT_CRITICAL_impl :=
Void ·OS_EXIT_CRITICAL·(⌞ ⌟)··{
  ⌞ ⌟;
  EXIT_CRITICAL
}·.

Definition DSP_C6x_Save_impl :=
Void ·DSP_C6x_Save·(⌞ ⌟)··{
  ⌞ ⌟;
  RETURN
}·.

Definition DSP_C6x_GetCurrentSP_impl :=
OS_STK ∗ ·DSP_C6x_GetCurrentSP·(⌞ ⌟)··{
  ⌞ ⌟;
  RETURN NULL
}·.

Definition DSP_C6x_Resume_impl :=
Void ·DSP_C6x_Resume·(⌞ ⌟)··{
  ⌞ ⌟;
  RETURN
}·. 
*)

Definition EXC_HANDLER_impl := fnull_impl.

Close Scope code_scope.
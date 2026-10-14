Require Import ios_int.
Require Import os_task.
Open Scope code_scope.

Definition int_lock_impl := 
    Int32 ·int_lock·(⌞ ⌟)··{
      ⌞level @ Int32⌟;

      ENTER_CRITICAL;ₛ
      level <- DINT;ₛ (*dint level*)
      EXIT_CRITICAL;ₛ
      RETURN level′ 
 }·.

Definition int_unlock_impl := 
    Void ·int_unlock·(⌞level @ Int32⌟)··{
      ⌞ ⌟;

      ENTER_CRITICAL;ₛ
      RINT (level);ₛ 
      EXIT_CRITICAL;ₛ
      RETURN
 }·.

Definition int_enable_pic_impl := 
    Void ·int_enable_pic·(⌞irqLine @ Int32u⌟)··{
      ⌞ ⌟;

      ENTER_CRITICAL;ₛ
      RINTP (irqLine);ₛ
      EXIT_CRITICAL;ₛ
      RETURN
 }·.

Definition int_disable_pic_impl := 
    Void ·int_disable_pic·(⌞irqLine @ Int32u⌟)··{
      ⌞ ⌟;
      
      ENTER_CRITICAL;ₛ
      DINTP (irqLine);ₛ
      EXIT_CRITICAL;ₛ
      RETURN
 }·.

Definition user_nmi_ISR_impl := 
  (*Void ·user_nmi_ISR·(⌞⌟)··{ *)
  user_nmi_ISR ↝ {
    (*⌞ y @ Int32 ⌟;*)

    (*DSP_C6x_Save(­);ₛ*)
    OSIntEnter(­);ₛ
    If(OSIntNesting′ ==ₑ ′1){
      (*y′ =ᶠ  DSP_C6x_GetCurrentSP(·);ₛ
      OSTCBCur′ → OSTCBStkPtr =ₑ 〈OS_STK ∗〉y′*)
      OSIntNesting′=ₑ′1
    };ₛ

    IF(exception_handler′ ==ₑ ′0){
      OSTaskSuspend(­  〈 Int8u 〉 ′OS_PRIO_SELF  ­)
    }ELSE{
      EXC_HANDLER(­)
    };ₛ
    EOI(1);ₛ
    OSIntExit(­);ₛ
    (*DSP_C6x_Resume(­);ₛ*)
    IRET
}.

Close Scope code_scope.

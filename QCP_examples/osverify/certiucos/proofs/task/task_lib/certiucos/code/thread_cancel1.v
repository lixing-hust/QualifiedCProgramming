
Require Import os_code_defs1.
Require Import code_notations1.
Require Import os_ucos_h1.


Open Scope code_scope.

(*
int pthread_cancel(pthread_t thread)
{
    /* Not allowed to delete idle task   */
	if (thread == (u32)OS_IDLE_PRIO) { 
		return ESRCH;
	}
    /* Task priority valid ?       */
	if ((thread >= OS_LOWEST_PRIO && thread != OS_PRIO_SELF) || 
  (thread != OS_PRIO_SELF && OSTCBPrioTbl[thread] == (OS_TCB)0) || 
  (OSTCBPrioTbl[OSPrioCur] == (OS_TCB)0)) {
        return (ESRCH);
	}

    PrioTbl[thread-1] = 0;

	if (OSTaskDel(thread)!=OS_NO_ERR) {
		return ESRCH;
	}
	return 0;
}
*)

Definition pthread_cancel_impl :=
Int8u ·pthread_cancel·(⌞thread @ Int8u⌟)··{
  ⌞ ret @ Int8u ⌟;
  
    If (thread′ ==ₑ ′OS_IDLE_PRIO) {
      RETURN ′ESRCH
    };ₛ
    If (thread′ ≥ ′OS_LOWEST_PRIO) {
      RETURN ′ESRCH
    };ₛ    
    ret′ =ᶠ OSTaskDel(·thread′·);ₛ
    If (ret′ !=ₑ ′OS_NO_ERR){
      RETURN ′ESRCH
    };ₛ
    RETURN ′OS_NO_ERR
}·. 

Definition pthread_exit_impl :=
Void ·pthread_exit·(⌞⌟)··{
  ⌞ 
    thread @ Int8u; 
    ret @ Int8u
    ⌟;
  
  ENTER_CRITICAL;ₛ   
  thread′ =ₑ OSTCBCur′→OSTCBPrio;ₛ 
  EXIT_CRITICAL;ₛ 
  ret′ =ᶠ OSTaskDel(·thread′·);ₛ
  RETURN
}·. 

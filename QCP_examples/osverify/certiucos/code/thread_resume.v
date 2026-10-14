Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import ios_cap_defs.


Open Scope code_scope.
Definition pthread_resume : ident := 1712%Z. 
Definition ESRCH : ident := 75%Z. 
Definition TASK_RESUME_CAP : ident := 16%Z. 


Definition pthread_resume_impl :=
  Int8u ·pthread_resume·(⌞thread@pthread_t⌟)··{
  ⌞ y@Int8u;
    ptcb@OS_TCB∗;
    pCSpace@CSPACE ∗⌟;
  ENTER_CRITICAL;ₛ
  y′ =ₑ OSTCBCur′→OSTCBPrio;ₛ
  If(OSRunning′ ==ₑ CFalse ||ₑ (OSRunning′ ==ₑ CTrue) &&ₑ (OSTCBPrioTbl′[y′]==ₑ〈OS_TCB ∗〉NULL)) {
      EXIT_CRITICAL;ₛ
      RETURN 〈Int8u〉′ESRCH
  };ₛ
  If(thread′ ==ₑ ′OS_IDLE_PRIO ||ₑ thread′ ≥ ′OS_LOWEST_PRIO) {
      EXIT_CRITICAL;ₛ
      RETURN 〈Int8u〉′ESRCH
  };ₛ
  ptcb′ =ₑOSTCBPrioTbl′[thread′];ₛ
  If(ptcb′ ==ₑ〈OS_TCB ∗〉NULL ) {
    EXIT_CRITICAL;ₛ
    RETURN 〈Int8u〉′ESRCH
  };ₛ
  If(ptcb′ ==ₑ &ₐ OSPlaceHolder′ ) {
    EXIT_CRITICAL;ₛ
    RETURN 〈Int8u〉′ESRCH
  };ₛ
  If((ptcb′→OSTCBStat &ₑ ′OS_STAT_SUSPEND) ==ₑ′OS_STAT_RDY) {
    EXIT_CRITICAL;ₛ
    RETURN 〈Int8u〉′EINVAL
  };ₛ
  pCSpace′ =ₑ OSCSpacePrioTbl′[y′];ₛ
  If(pCSpace′ ==ₑ〈CSPACE∗〉 NULL){
    EXIT_CRITICAL;ₛ
    RETURN 〈Int8u〉′USER_CAPABILITY_NONE
  };ₛ
  If((pCSpace′→cnode..slots[′CAP_TASK_CLASS]
  ..capability..cap_content..category..category_right &ₑ ′TASK_RESUME_CAP) ==ₑ ′0){
    EXIT_CRITICAL;ₛ
    RETURN 〈Int8u〉′USER_CAPABILITY_NONE
  };ₛ
    EXIT_CRITICAL;ₛ

    scall OSTaskResume(〈Int8u〉thread′::nil);ₛ
    RETURN 〈Int8u〉′0
  }·.



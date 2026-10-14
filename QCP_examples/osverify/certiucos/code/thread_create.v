
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.


Open Scope code_scope.


(*Definition attr: ident := 1706%Z. 

Definition sched_param_t : type := 
  STRUCT sched_param ­{ 
                        ⌞sched_priority @ Int32
                      ⌟
                        }­.
*)



Definition pthread_create_impl :=
Int8u ·pthread_create·(⌞thread @ Int32u∗; attr @ pthread_attr_t∗; start_routine @ Void∗; arg @ Void∗⌟)··{
       ⌞ ret @ Int8u;
          x @ Int8s;
          y @ Int8s;
          z @ Int8s;
          prio @ Int8u
    ⌟;

    x′ =ᶠ UserAddrCheck(·〈Int32u∗〉 attr′·);ₛ 
    If (x′ ==ₑ ′0) {
      RETURN ′EINVAL
    };ₛ
    y′ =ᶠ UserAddrCheck(·thread′·);ₛ 
    If (y′ ==ₑ ′0) {
      RETURN ′EINVAL
    };ₛ
    z′ =ᶠ UserAddrCheck(·〈Int32u∗〉start_routine′·);ₛ 
    If (z′ ==ₑ ′0) {
      RETURN ′EINVAL
    };ₛ

    ENTER_CRITICAL;ₛ
    If (attr′→sched_priority >ₑ ′OS_LOWEST_PRIO) {
      EXIT_CRITICAL;ₛ
      RETURN ′EINVAL
    };ₛ 

    If (OSTCBPrioTbl′[attr′→sched_priority] !=ₑ NULL){
      EXIT_CRITICAL;ₛ
      RETURN ′EAGAIN
    };ₛ
    prio′ =ₑ attr′→sched_priority;ₛ
    EXIT_CRITICAL;ₛ
    
    (* ∗thread′ =ₑ attr′→sched_priority;ₛ *)
    ret′ =ᶠ OSTaskCreate(·start_routine′, arg′, prio′·);ₛ
    If (ret′ ==ₑ ′OS_NO_MORE_TCB){
      RETURN ′EAGAIN
    };ₛ
    RETURN ′OS_NO_ERR
}·. 

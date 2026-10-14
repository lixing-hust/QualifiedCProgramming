
Require Import PIF_os_code_defs.
Require Import PIF_code_notations.
Require Import PIF_os_ucos_h.

(* Require Import useraddrcheck. *)

Open Scope code_scope.

Definition PlaceHolder:= &ₐ OSPlaceHolder′.

Definition ad: ident := 991%Z. 
Definition ptb: ident := 992%Z.
Definition flag: ident := 993%Z.
Definition PTHREAD_CANCEL_UNSAFE:ident := 1%Z.
Definition pthread_mutexattr_init_impl := 
Int32 ·pthread_mutexattr_init·(⌞attr @ pthread_mutexattr_t∗⌟)··{
        ⌞ 
          i @ Int32;
          flag @ Int32;
          ptb @ OS_TCB∗;
          ad @ Int32u∗;
          x @ Int8s
        ⌟;
          ad′ =ₑ  〈Int32u∗〉 attr′;ₛ
          x′ =ᶠ UserAddrCheck(·(* 〈Int32u〉 *)ad′·);ₛ
         If (x′ ==ₑ ′0){
            RETURN ′EINVAL
        };ₛ 
        ENTER_CRITICAL;ₛ
        attr′→is_initialized =ₑ ′1;ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
	      attr′→process_shared =ₑ ′1;ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        OSPrioCur′ =ₑ OSTCBCur′→OSTCBPrio;ₛ
	      attr′→prio_ceiling =ₑ OSPrioCur′;ₛ
        EXIT_CRITICAL;ₛ
        flag′ =ₑ ′1;ₛ
        i′ =ₑ ′0;ₛ
        WHILE ( (i′ <ₑ (′OS_LOWEST_PRIO +ₑ ′1)) &&ₑ  flag′ ){
           ENTER_CRITICAL;ₛ
	         ptb′ =ₑ OSTCBPrioTbl′[i′];ₛ
           EXIT_CRITICAL;ₛ
           IF ( ptb′ ==ₑ NULL){
                ENTER_CRITICAL;ₛ
                attr′→prio_ceiling =ₑ i′;ₛ
                EXIT_CRITICAL;ₛ
                flag′ =ₑ ′0
            }ELSE{
                ++ i′
           }
        };ₛ
        ENTER_CRITICAL;ₛ
        attr′→protocol =ₑ ′PTHREAD_PRIO_INHERIT;ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
	      attr′→recursive =ₑ ′PTHREAD_MUTEX_ERRORCHECK;ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
	      attr′→cancel_safe =ₑ ′PTHREAD_CANCEL_UNSAFE;ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
	      attr′→waitq_type =ₑ ′0;ₛ
        EXIT_CRITICAL;ₛ
        RETURN ′0 
}· .

Definition pthread_mutexattr_destroy_impl := 
Int32 ·pthread_mutexattr_destroy·(⌞attr @ pthread_mutexattr_t ∗⌟)··{
        ⌞ 
          ad @ Int32u∗;
          x @ Int8s
        ⌟;
          ad′ =ₑ  〈Int32u∗〉 attr′;ₛ
          x′ =ᶠ UserAddrCheck(·(* 〈Int32u〉 *)ad′·);ₛ
         If (x′ ==ₑ ′0){
            RETURN ′EINVAL
        };ₛ 
        ENTER_CRITICAL;ₛ
        attr′→is_initialized =ₑ ′0;ₛ
        EXIT_CRITICAL;ₛ
        RETURN ′0
}· .

Definition init: ident := 990%Z.

Definition pthread_mutexattr_settype_impl := 
Int32 ·pthread_mutexattr_settype·(⌞attr @ pthread_mutexattr_t ∗; mutex_type @ Int32⌟)··{
        ⌞
          ad @ Int32u∗; 
          init @ Int32;
          x @ Int8s
        ⌟;
          ad′ =ₑ  〈Int32u∗〉 attr′;ₛ
          x′ =ᶠ UserAddrCheck(·(* 〈Int32u〉 *)ad′·);ₛ
         If (x′ ==ₑ ′0){
            RETURN ′EINVAL
        };ₛ 
        ENTER_CRITICAL;ₛ
        init′  =ₑ attr′→is_initialized;ₛ
        EXIT_CRITICAL;ₛ
         If (init′  ==ₑ ′0) {
         RETURN ′EINVAL
        };ₛ
        If  ((mutex_type′ <ₑ ′0) ||ₑ (mutex_type′ >ₑ ′PTHREAD_MUTEX_DEFAULT)){
         RETURN ′EINVAL
        };ₛ
        If (mutex_type′ ==ₑ ′PTHREAD_MUTEX_DEFAULT){
         mutex_type′ =ₑ ′PTHREAD_MUTEX_ERRORCHECK
        };ₛ 
        ENTER_CRITICAL;ₛ
        attr′→recursive =ₑ mutex_type′;ₛ
        EXIT_CRITICAL;ₛ
        RETURN ′0
}· .

Definition mtp: ident := 989%Z. 

Definition pthread_mutexattr_gettype_impl := 
Int32 ·pthread_mutexattr_gettype·(⌞attr @ (* const *)pthread_mutexattr_t ∗; mutex_type @ Int32 ∗⌟)··{
        ⌞ 
          ad @ Int32u∗; 
          mtp @ Int32u∗; 
          init @ Int32;
          x @ Int8s;
          y @ Int8s
        ⌟;
        ad′ =ₑ  〈Int32u∗〉 attr′;ₛ
        x′ =ᶠ UserAddrCheck(·ad′·);ₛ
         If (x′ ==ₑ ′0){
            RETURN ′EINVAL
        };ₛ 
        mtp′ =ₑ  〈Int32u∗〉mutex_type′;ₛ
        y′ =ᶠ UserAddrCheck(·mtp′·);ₛ
         If (y′ ==ₑ ′0){
            RETURN ′EINVAL
        };ₛ 
        ENTER_CRITICAL;ₛ
        init′  =ₑ attr′→is_initialized;ₛ
        EXIT_CRITICAL;ₛ
         If (init′  ==ₑ ′0) {
         RETURN ′EINVAL
        };ₛ
        ENTER_CRITICAL;ₛ
        ∗mutex_type′ =ₑ attr′→recursive;ₛ
        EXIT_CRITICAL;ₛ
        RETURN ′0 
}· .

Definition pthread_mutexattr_setprioceiling_impl := 
Int32 ·pthread_mutexattr_setprioceiling·(⌞attr @ pthread_mutexattr_t ∗; prioceiling @ Int32⌟)··{
        ⌞ 
          ad @ Int32u∗;
          init @ Int32;
          x @ Int8s
        ⌟;
          ad′ =ₑ  〈Int32u∗〉 attr′;ₛ
          x′ =ᶠ UserAddrCheck(·(* 〈Int32u〉 *)ad′·);ₛ
          If (x′ ==ₑ ′0){
            RETURN ′EINVAL
          };ₛ 
         ENTER_CRITICAL;ₛ
         init′  =ₑ attr′→is_initialized;ₛ
         EXIT_CRITICAL;ₛ
         If (init′  ==ₑ ′0) {
         RETURN ′EINVAL
        };ₛ
         If ( (prioceiling′<ₑ ′0) ||ₑ (prioceiling′ >ₑ  ′OS_MAX_TASKS)){
         RETURN ′EINVAL
         };ₛ
          ENTER_CRITICAL;ₛ
          If (OSTCBPrioTbl′[prioceiling′]  !=ₑ (* 〈OS_TCB ∗〉 ′0 *) NULL){
          EXIT_CRITICAL;ₛ
          RETURN ′EINVAL
         };ₛ
           attr′→prio_ceiling =ₑ prioceiling′;ₛ
           EXIT_CRITICAL;ₛ
           RETURN ′0
}· .

Definition pc: ident := 988%Z.

Definition pthread_mutexattr_getprioceiling_impl := 
Int32 ·pthread_mutexattr_getprioceiling·(⌞attr @ (* const *)pthread_mutexattr_t ∗; prioceiling @ Int32 ∗⌟)··{
        ⌞ 
          ad @ Int32u∗; 
          pc @ Int32u∗; 
          init @ Int32;
          x @ Int8s;
          y @ Int8s
        ⌟;
        ad′ =ₑ  〈Int32u∗〉 attr′;ₛ
        x′ =ᶠ UserAddrCheck(·ad′·);ₛ
         If (x′ ==ₑ ′0){
            RETURN ′EINVAL
        };ₛ 
        pc′ =ₑ  〈Int32u∗〉prioceiling′;ₛ
        y′ =ᶠ UserAddrCheck(·pc′·);ₛ
         If (y′ ==ₑ ′0){
            RETURN ′EINVAL
        };ₛ 
        ENTER_CRITICAL;ₛ
        init′  =ₑ attr′→is_initialized;ₛ
        EXIT_CRITICAL;ₛ
         If (init′  ==ₑ ′0) {
         RETURN ′EINVAL
        };ₛ
        ENTER_CRITICAL;ₛ
        ∗prioceiling′ =ₑ attr′→prio_ceiling;ₛ
        EXIT_CRITICAL;ₛ
        RETURN ′0 
}· .

Definition pric: ident := 994%Z.
Definition cpr: ident := 996%Z.
Definition r: ident := 997%Z.
Definition ty: ident := 998%Z.
Definition muxowner: ident := 999%Z.

Definition pthread_mutex_trylock_impl := 
Int32 ·pthread_mutex_trylock·(⌞mutex @ pthread_mutex_t∗⌟)··{
         ⌞ 
          err @ Int8u;
          pos @ Int32s;
          x @ Int8s;
          z @ Int8u;
          muxowner @ Int8u;
          ty @ Int32;
          r @ Int32;
          cpr @ Int8u;
          pric @ Int32;
          p @ OS_EVENT∗
        ⌟;
        x′ =ᶠ UserAddrCheck(·(* 〈Int32u〉 *)mutex′·);ₛ
        IF(x′ ==ₑ ′0){
         pos′ =ₑ ′-1
         }ELSE{
         ENTER_CRITICAL;ₛ
         pos′ =ₑ ∗mutex′;ₛ
         EXIT_CRITICAL
        };ₛ
        If ((pos′ <ₑ ′0 ) ||ₑ (pos′ ≥ (′OS_USER_MAX_EVENTS÷ ′3) )){
         RETURN ′EINVAL
         };ₛ

        ENTER_CRITICAL;ₛ
        p′ =ₑ efield (Pthread_Mutex′[pos′]) pevent;ₛ
        EXIT_CRITICAL;ₛ
        If (p′ ==ₑ NULL) {
            RETURN ′EINVAL
        };ₛ

          ENTER_CRITICAL;ₛ
          p′ =ₑ efield (Pthread_Mutex′[pos′]) pevent;ₛ 
          IF (p′ !=ₑ NULL) {
          muxowner′ =ₑ〈Int8u〉( (efield (Pthread_Mutex′[pos′]) pevent) →OSEventCnt &ₑ ′OS_MUTEX_KEEP_LOWER_8)
          }ELSE{
          EXIT_CRITICAL;ₛ
          RETURN ′EINVAL
        };ₛ
          EXIT_CRITICAL;ₛ

        ENTER_CRITICAL;ₛ
        ty′ =ₑ efield (Pthread_Mutex′[pos′]) mutex_type;ₛ
        EXIT_CRITICAL;ₛ
        If ( ty′ ==ₑ  ′PTHREAD_MUTEX_RECURSIVE){
           ENTER_CRITICAL;ₛ
           cpr′ =ₑ OSTCBCur′→OSTCBPrio;ₛ
           EXIT_CRITICAL;ₛ
            ENTER_CRITICAL;ₛ
           pric′ =ₑ efield (Pthread_Mutex′[pos′])prio_ceiling;ₛ
           EXIT_CRITICAL;ₛ
          If (muxowner′ ==ₑ  cpr′ ||ₑ pric′ ==ₑ  cpr′){
            ENTER_CRITICAL;ₛ
            r′ =ₑ efield (Pthread_Mutex′[pos′]) recursive_cnt;ₛ
            EXIT_CRITICAL;ₛ
            IF ( r′ <ₑ ′PTHREAD_MUTEX_RECURSIVE_MAX){
            ENTER_CRITICAL;ₛ
            efield (Pthread_Mutex′[pos′]) recursive_cnt =ₑ efield (Pthread_Mutex′[pos′]) recursive_cnt +ₑ ′1;ₛ
            EXIT_CRITICAL;ₛ
            RETURN ′0
         }ELSE{
            RETURN ′EAGAIN
                   } 
           }
         };ₛ
        ENTER_CRITICAL;ₛ
        p′ =ₑ efield (Pthread_Mutex′[pos′]) pevent;ₛ
        OSTCBCur′→__OSTskMuxPtr =ₑ p′;ₛ 
        EXIT_CRITICAL;ₛ
         z′ =ᶠ OSMutexAccept(·p′·);ₛ

        ENTER_CRITICAL;ₛ
        OSTCBCur′→__OSTskMuxPtr =ₑ NULL;ₛ 
        EXIT_CRITICAL;ₛ

         If (z′ ==ₑ  ′1){
          ENTER_CRITICAL;ₛ
          p′ =ₑ efield (Pthread_Mutex′[pos′]) pevent;ₛ
          If (p′ !=ₑ NULL) {
          (efield (Pthread_Mutex′[pos′] ) mutex_owner) =ₑ 〈Int8u〉((efield (Pthread_Mutex′[pos′] ) pevent)→OSEventCnt &ₑ ′OS_MUTEX_KEEP_LOWER_8)
          };ₛ
          EXIT_CRITICAL;ₛ
          RETURN ′0
          };ₛ
          RETURN ′EBUSY
}· .

Definition pthread_mutex_init_impl := 
Int32 ·pthread_mutex_init·(⌞
              mutex @ pthread_mutex_t∗; attr @ (* const *)pthread_mutexattr_t∗;
              attrEntity @ pthread_mutexattr_t∗; err @ Int8u∗⌟)··{
         ⌞ 
          i @ Int32;
          prio @ Int32;
          pos @ Int32s;
          x @ Int8s;
          y @ long;
          z @ Int32;
          p @ OS_EVENT ∗
        ⌟;
         i′ =ₑ ′0;ₛ
         prio′ =ₑ ′0 − ′1;ₛ
        x′ =ᶠ UserAddrCheck(·〈Int32u∗〉mutex′·);ₛ
        If (x′ ==ₑ ′0){
            RETURN ′EINVAL
        };ₛ
        If (attr′ ==ₑ NULL){
             z′ =ᶠ pthread_mutexattr_init (· attrEntity′ ·);ₛ
            If (z′ !=ₑ ′0){
              RETURN ′EINVAL
            };ₛ
          attr′ =ₑ attrEntity′
        };ₛ
        ENTER_CRITICAL;ₛ 
        x′ =ᶠ getFreePos(·′1·);ₛ 
        pos′ =ₑ 〈Int32〉 x′;ₛ
        If(pos′ ==ₑ ′255){
              EXIT_CRITICAL;ₛ 
              RETURN ′EAGAIN
        };ₛ
        efield (Pthread_Mutex′[pos′] ) pevent  =ₑ 〈OS_EVENT ∗〉 PlaceHolder;ₛ 
        EXIT_CRITICAL;ₛ 

        ENTER_CRITICAL;ₛ
        y′ =ₑ attr′→prio_ceiling;ₛ
        EXIT_CRITICAL;ₛ
        p′ =ᶠ OSMutexCreate(·〈Int8u〉y′, (* &ₐ *)err′·);ₛ 
        ENTER_CRITICAL;ₛ
        efield (Pthread_Mutex′[pos′] ) pevent  =ₑ p′;ₛ 
        OSTCBCur′→__OSTskMuxPtr =ₑ NULL;ₛ
        OSTCBCur′→__OSTskEvLoc =ₑ ′__EvLoc_normal;ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
         x′ =ₑ ∗err′;ₛ
        EXIT_CRITICAL;ₛ
        If (x′ !=ₑ ′OS_NO_ERR){
           RETURN ′EAGAIN
        };ₛ

        ENTER_CRITICAL;ₛ
        (efield (Pthread_Mutex′[pos′] ) cancel_safe) =ₑ attr′→cancel_safe;ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        (efield (Pthread_Mutex′[pos′] ) protocol)=ₑ attr′→protocol;ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        (efield (Pthread_Mutex′[pos′] ) recursive_cnt)=ₑ ′0;ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        (efield (Pthread_Mutex′[pos′] ) mutex_owner) =ₑ ′255;ₛ
        EXIT_CRITICAL;ₛ
         ENTER_CRITICAL;ₛ
        (efield (Pthread_Mutex′[pos′] ) prio_ceiling)=ₑ attr′→prio_ceiling;ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        (efield (Pthread_Mutex′[pos′] ) mutex_type) =ₑ attr′→ recursive;ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        (efield (Pthread_Mutex′[pos′] ) waitq_type) =ₑ attr′→ waitq_type;ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        ∗mutex′ =ₑ pos′;ₛ
        EXIT_CRITICAL;ₛ
        RETURN ′0 
}· .
Definition UserAddrCheckCrit := 288%Z. 
Definition pthread_mutex_destroy_impl :=
Int32 ·pthread_mutex_destroy·(⌞mutex @ pthread_mutex_t∗⌟)··{
         ⌞
          x @ Int8s;
          pos @ Int32;
          p @ OS_EVENT ∗
        ⌟;

        ENTER_CRITICAL;ₛ
        x′ =ᶠ UserAddrCheckCrit(·〈Int32u∗〉mutex′·);ₛ
        IF(x′ ==ₑ ′0){
            pos′ =ₑ ′-1
        }ELSE{
            pos′ =ₑ ∗mutex′
        };ₛ
        If ((pos′ <ₑ ′0 ) ||ₑ (pos′ ≥ (′OS_USER_MAX_EVENTS÷ ′3))){
            EXIT_CRITICAL;ₛ
            RETURN ′EINVAL
        };ₛ
        p′ =ₑ efield (Pthread_Mutex′[pos′]) pevent;ₛ
        If (p′ ==ₑ NULL) {
            EXIT_CRITICAL;ₛ
            RETURN ′EINVAL
        };ₛ
        If (((efield (Pthread_Mutex′[pos′] ) pevent)→OSEventGrp !=ₑ ′0) ||ₑ (OSIntNesting′ >ₑ ′0)){
            EXIT_CRITICAL;ₛ
            RETURN ′EBUSY
        };ₛ

        p′ =ₑ efield (Pthread_Mutex′[pos′] ) pevent;ₛ 
        efield (Pthread_Mutex′[pos′] ) pevent =ₑ 〈OS_EVENT ∗〉NULL;ₛ
        OSMutexDel(­ p′ ­);ₛ

        EXIT_CRITICAL;ₛ

        RETURN ′0
}· .

Definition pthread_mutex_lock_impl := 
Int32 ·pthread_mutex_lock·(⌞mutex @ pthread_mutex_t∗⌟)··{
         ⌞ 
          err @ Int8u;
          pos @ Int32s;
          x @ Int8s;
          z @ Int8u;
          muxowner @ Int8u;
          ty @ Int32;
          pip @ Int32;
          r @ Int32;
          cpr @ Int8u;
          p @ OS_EVENT∗
        ⌟;
        x′ =ᶠ UserAddrCheck(·(* 〈Int32u〉 *)mutex′·);ₛ
        IF(x′ ==ₑ ′0){
         pos′ =ₑ ′-1
         }ELSE{
         ENTER_CRITICAL;ₛ
         pos′ =ₑ ∗mutex′;ₛ
         EXIT_CRITICAL
        };ₛ
        If ((pos′ <ₑ ′0 ) ||ₑ (pos′ ≥ (′OS_USER_MAX_EVENTS÷ ′3) )){
         RETURN ′EINVAL
         };ₛ

        ENTER_CRITICAL;ₛ
        p′ =ₑ efield (Pthread_Mutex′[pos′]) pevent;ₛ
        EXIT_CRITICAL;ₛ
        If (p′ ==ₑ NULL) {
            RETURN ′EINVAL
        };ₛ

          ENTER_CRITICAL;ₛ
          p′ =ₑ efield (Pthread_Mutex′[pos′]) pevent;ₛ 
          IF (p′ !=ₑ NULL) {
          muxowner′ =ₑ〈Int8u〉( (efield (Pthread_Mutex′[pos′]) pevent) →OSEventCnt &ₑ ′OS_MUTEX_KEEP_LOWER_8)
          }ELSE{
          EXIT_CRITICAL;ₛ
          RETURN ′EINVAL
        };ₛ
          EXIT_CRITICAL;ₛ

        ENTER_CRITICAL;ₛ
        ty′ =ₑ efield (Pthread_Mutex′[pos′]) mutex_type;ₛ
        EXIT_CRITICAL;ₛ

        If ( ty′ !=ₑ  ′PTHREAD_MUTEX_NORMAL &&ₑ ty′ !=ₑ  ′PTHREAD_MUTEX_ERRORCHECK 
              &&ₑ ty′ !=ₑ  ′PTHREAD_MUTEX_RECURSIVE)
        {
          RETURN ′EINVAL
        };ₛ

        If ( ty′ ==ₑ  ′PTHREAD_MUTEX_ERRORCHECK){
         ENTER_CRITICAL;ₛ
         cpr′ =ₑ OSTCBCur′→OSTCBPrio;ₛ
         EXIT_CRITICAL;ₛ
         ENTER_CRITICAL;ₛ
         pip′ =ₑ efield (Pthread_Mutex′[pos′]) prio_ceiling;ₛ
         EXIT_CRITICAL;ₛ
          If(muxowner′ ==ₑ  cpr′ ||ₑ pip′ ==ₑ cpr′){
          RETURN ′EDEADLK
          }
        };ₛ

        If ( ty′ ==ₑ  ′PTHREAD_MUTEX_RECURSIVE){
           ENTER_CRITICAL;ₛ
           cpr′ =ₑ OSTCBCur′→OSTCBPrio;ₛ
           EXIT_CRITICAL;ₛ
           ENTER_CRITICAL;ₛ
           pip′ =ₑ efield (Pthread_Mutex′[pos′]) prio_ceiling;ₛ
           EXIT_CRITICAL;ₛ
          If (muxowner′ ==ₑ  cpr′ ||ₑ pip′ ==ₑ cpr′){
            ENTER_CRITICAL;ₛ
            r′ =ₑ efield (Pthread_Mutex′[pos′]) recursive_cnt;ₛ
            EXIT_CRITICAL;ₛ
            IF ( r′ <ₑ ′PTHREAD_MUTEX_RECURSIVE_MAX){
            ENTER_CRITICAL;ₛ
            efield (Pthread_Mutex′[pos′]) recursive_cnt =ₑ efield (Pthread_Mutex′[pos′]) recursive_cnt +ₑ ′1;ₛ
            EXIT_CRITICAL;ₛ
            RETURN ′0
         }ELSE{
            RETURN ′EAGAIN
                   } 
           }
         };ₛ

        ENTER_CRITICAL;ₛ
        p′ =ₑ efield (Pthread_Mutex′[pos′]) pevent;ₛ
        OSTCBCur′→__OSTskMuxPtr =ₑ p′;ₛ
        EXIT_CRITICAL;ₛ
         z′ =ᶠ OSMutexPend(·p′, 〈Int16u〉 ′0·);ₛ

         ENTER_CRITICAL;ₛ
        OSTCBCur′→__OSTskMuxPtr =ₑ NULL;ₛ
        EXIT_CRITICAL;ₛ

         If (z′ ==ₑ  ′OS_NO_ERR){
          ENTER_CRITICAL;ₛ
          p′ =ₑ efield (Pthread_Mutex′[pos′]) pevent;ₛ
          If (p′ !=ₑ NULL) {
          (efield (Pthread_Mutex′[pos′] ) mutex_owner) =ₑ 〈Int8u〉((efield (Pthread_Mutex′[pos′] ) pevent)→OSEventCnt &ₑ ′OS_MUTEX_KEEP_LOWER_8)
          };ₛ
          EXIT_CRITICAL;ₛ
          RETURN ′0
          };ₛ
          RETURN ′EINVAL
}· .

Definition pthread_mutex_timedlock_impl := 
Int32 ·pthread_mutex_timedlock·(⌞mutex @ pthread_mutex_t∗; abs_timeout @ Int16u⌟)··{
         ⌞ 
          err @ Int8u;
          pos @ Int32s;
          x @ Int8s;
          z @ Int8u;
          muxowner @ Int8u;
          ty @ Int32;
          pip @ Int32;
          r @ Int32;
          cpr @ Int8u;
          p @ OS_EVENT∗
        ⌟;
        x′ =ᶠ UserAddrCheck(·(* 〈Int32u〉 *)mutex′·);ₛ
        IF(x′ ==ₑ ′0){
         pos′ =ₑ ′-1
         }ELSE{
         ENTER_CRITICAL;ₛ
         pos′ =ₑ ∗mutex′;ₛ
         EXIT_CRITICAL
        };ₛ
        If ((pos′ <ₑ ′0 ) ||ₑ (pos′ ≥ (′OS_USER_MAX_EVENTS÷ ′3) )(* ||ₑ(efield (Pthread_Mutex′[pos′] ) pevent ==ₑ NULL) *)){
         RETURN ′EINVAL
         };ₛ

        If ((abs_timeout′ ==ₑ ′0 ) ||ₑ (abs_timeout′ >ₑ ′65535 )){
         RETURN ′EINVAL
         };ₛ

        ENTER_CRITICAL;ₛ
        p′ =ₑ efield (Pthread_Mutex′[pos′]) pevent;ₛ
        EXIT_CRITICAL;ₛ
        If (p′ ==ₑ NULL) {
            RETURN ′EINVAL
        };ₛ

          ENTER_CRITICAL;ₛ
          p′ =ₑ efield (Pthread_Mutex′[pos′]) pevent;ₛ 
          IF (p′ !=ₑ NULL) {
          muxowner′ =ₑ〈Int8u〉( (efield (Pthread_Mutex′[pos′]) pevent) →OSEventCnt &ₑ ′OS_MUTEX_KEEP_LOWER_8)
          }ELSE{
          EXIT_CRITICAL;ₛ
          RETURN ′EINVAL
        };ₛ
          EXIT_CRITICAL;ₛ

        ENTER_CRITICAL;ₛ
        ty′ =ₑ efield (Pthread_Mutex′[pos′]) mutex_type;ₛ
        EXIT_CRITICAL;ₛ

        If ( ty′ !=ₑ  ′PTHREAD_MUTEX_NORMAL &&ₑ ty′ !=ₑ  ′PTHREAD_MUTEX_ERRORCHECK 
              &&ₑ ty′ !=ₑ  ′PTHREAD_MUTEX_RECURSIVE)
        {
          RETURN ′EINVAL
        };ₛ

        If ( ty′ ==ₑ  ′PTHREAD_MUTEX_ERRORCHECK){
         ENTER_CRITICAL;ₛ
         cpr′ =ₑ OSTCBCur′→OSTCBPrio;ₛ
         EXIT_CRITICAL;ₛ
         ENTER_CRITICAL;ₛ
         pip′ =ₑ efield (Pthread_Mutex′[pos′]) prio_ceiling;ₛ
         EXIT_CRITICAL;ₛ
          If(muxowner′ ==ₑ  cpr′ ||ₑ pip′ ==ₑ cpr′){
          RETURN ′EDEADLK
          }
        };ₛ

        If ( ty′ ==ₑ  ′PTHREAD_MUTEX_RECURSIVE){
           ENTER_CRITICAL;ₛ
           cpr′ =ₑ OSTCBCur′→OSTCBPrio;ₛ
           EXIT_CRITICAL;ₛ
           ENTER_CRITICAL;ₛ
           pip′ =ₑ efield (Pthread_Mutex′[pos′]) prio_ceiling;ₛ
           EXIT_CRITICAL;ₛ
          If (muxowner′ ==ₑ  cpr′ ||ₑ pip′ ==ₑ cpr′){
            ENTER_CRITICAL;ₛ
            r′ =ₑ efield (Pthread_Mutex′[pos′]) recursive_cnt;ₛ
            EXIT_CRITICAL;ₛ
            IF ( r′ <ₑ ′PTHREAD_MUTEX_RECURSIVE_MAX){
            ENTER_CRITICAL;ₛ
            efield (Pthread_Mutex′[pos′]) recursive_cnt =ₑ efield (Pthread_Mutex′[pos′]) recursive_cnt +ₑ ′1;ₛ
            EXIT_CRITICAL;ₛ
            RETURN ′0
         }ELSE{
            RETURN ′EAGAIN
                   } 
           }
         };ₛ

        ENTER_CRITICAL;ₛ
        p′ =ₑ efield (Pthread_Mutex′[pos′]) pevent;ₛ
        OSTCBCur′→__OSTskMuxPtr =ₑ p′;ₛ
        EXIT_CRITICAL;ₛ
         z′ =ᶠ OSMutexPend(·p′, abs_timeout′·);ₛ
         ENTER_CRITICAL;ₛ
        OSTCBCur′→__OSTskMuxPtr =ₑ NULL;ₛ
        EXIT_CRITICAL;ₛ
         If (z′ ==ₑ  ′OS_TIMEOUT){
          RETURN ′ETIMEDOUT
          };ₛ
         If (z′ ==ₑ  ′OS_NO_ERR){
          ENTER_CRITICAL;ₛ
          p′ =ₑ efield (Pthread_Mutex′[pos′]) pevent;ₛ
          If (p′ !=ₑ NULL) {
          (efield (Pthread_Mutex′[pos′] ) mutex_owner) =ₑ 〈Int8u〉((efield (Pthread_Mutex′[pos′] ) pevent)→OSEventCnt &ₑ ′OS_MUTEX_KEEP_LOWER_8)
          };ₛ
          EXIT_CRITICAL;ₛ
          RETURN ′0
          };ₛ
          RETURN ′EINVAL
}· .

Definition cal: ident := 995%Z.

Definition pthread_mutex_unlock_impl := 
Int32 ·pthread_mutex_unlock·(⌞mutex @ pthread_mutex_t∗⌟)··{
         ⌞ 
          x @ Int8s;
          pos @ Int32s;
          ret @ Int32;
          muxowner @ Int8u;
          ty @ Int32;
          r @ Int32;
          cpr @ Int8u;
          cal @ Int8u;
          pric @ Int32;
          p @ OS_EVENT∗
        ⌟;
        x′ =ᶠ UserAddrCheck(·(* 〈Int32u〉 *)mutex′·);ₛ
        IF(x′ ==ₑ ′0){
         pos′ =ₑ ′-1
         }ELSE{
         ENTER_CRITICAL;ₛ
         pos′ =ₑ ∗mutex′;ₛ
         EXIT_CRITICAL
        };ₛ
        If ((pos′ <ₑ ′0 ) ||ₑ (pos′ ≥ (′OS_USER_MAX_EVENTS÷ ′3))){
         RETURN ′EINVAL
         };ₛ

        ENTER_CRITICAL;ₛ
        p′ =ₑ efield (Pthread_Mutex′[pos′]) pevent;ₛ
        EXIT_CRITICAL;ₛ
        If (p′ ==ₑ NULL) {
            RETURN ′EINVAL
        };ₛ

          ENTER_CRITICAL;ₛ
          p′ =ₑ efield (Pthread_Mutex′[pos′]) pevent;ₛ 
          IF (p′ !=ₑ NULL) {
          muxowner′ =ₑ〈Int8u〉( (efield (Pthread_Mutex′[pos′]) pevent) →OSEventCnt &ₑ ′OS_MUTEX_KEEP_LOWER_8)
          }ELSE{
          EXIT_CRITICAL;ₛ
          RETURN ′EINVAL
        };ₛ
          EXIT_CRITICAL;ₛ

        ENTER_CRITICAL;ₛ
        ty′ =ₑ efield (Pthread_Mutex′[pos′]) mutex_type;ₛ
        EXIT_CRITICAL;ₛ
        If ( ty′ ==ₑ  ′PTHREAD_MUTEX_RECURSIVE){

           ENTER_CRITICAL;ₛ
           cpr′ =ₑ OSTCBCur′→OSTCBPrio;ₛ
           EXIT_CRITICAL;ₛ
           ENTER_CRITICAL;ₛ
           pric′ =ₑ efield (Pthread_Mutex′[pos′])prio_ceiling;ₛ
           EXIT_CRITICAL;ₛ

          IF (muxowner′ ==ₑ  cpr′ ||ₑ pric′ ==ₑ  cpr′){

            ENTER_CRITICAL;ₛ
            −− efield (Pthread_Mutex′[pos′]) recursive_cnt;ₛ
            EXIT_CRITICAL;ₛ

            ENTER_CRITICAL;ₛ
            r′ =ₑ efield (Pthread_Mutex′[pos′]) recursive_cnt;ₛ
            EXIT_CRITICAL;ₛ
              If (r′ !=ₑ ′0) {
                RETURN ′0
               }
          }ELSE{
            RETURN ′EPERM
             } 
         };ₛ

        ENTER_CRITICAL;ₛ
        p′ =ₑ efield (Pthread_Mutex′[pos′]) pevent;ₛ
        OSTCBCur′→__OSTskMuxPtr =ₑ p′;ₛ 
        EXIT_CRITICAL;ₛ
        cal′ =ᶠ OSMutexPost(·p′·) ;ₛ 
        ENTER_CRITICAL;ₛ
        OSTCBCur′→__OSTskMuxPtr =ₑ NULL;ₛ 
        EXIT_CRITICAL;ₛ
        ret′ =ₑ  〈Int32〉 cal′ ;ₛ
        If (ret′  ==ₑ ′ OS_ERR_NOT_MUTEX_OWNER){
         RETURN ′EPERM
         };ₛ
         IF(ret′  !=ₑ ′0){
         RETURN ′EINVAL
         }ELSE{
                RETURN ′0
         }
}· .

Close Scope code_scope.

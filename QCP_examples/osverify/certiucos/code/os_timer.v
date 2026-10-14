Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.


Open Scope code_scope.
Definition f := fun (x : nat) => x= 1. 

(** 文中所有的  Timer_TGCR = <unsigned int *> (TGCR_REG + (timerid ≪ 16)) 
    改为 〈Int32u ∗〉((__timerregs′ +ₑ ′9 ) +ₑ (timerid′ ≪ ′14 ))  
   **)

Definition sys_clk_rate_get_impl := 
      Int32u ·sys_clk_rate_get·(⌞ ⌟)··{
             ⌞ tickspersecond @ Int32 ⌟; 
             ENTER_CRITICAL;ₛ
             tickspersecond′ =ₑ OS_TICKS_PER_SEC_SYS′;ₛ
             EXIT_CRITICAL;ₛ
             RETURN tickspersecond′
             }·.

Notation "'-1'" := (Zneg xH).

Definition sys_clk_rate_set_impl := 
      Int32 ·sys_clk_rate_set·(⌞tickspersecond @ Int32⌟)··{
      ⌞
       err @ Int32u;
       prdlo @ Int32u
      ⌟; 
      If(tickspersecond′ <ₑ ′1){
            err′ =ₑ ′EINVAL;ₛ
            RETURN ′-1 
      };ₛ
      ENTER_CRITICAL;ₛ
      OS_TICKS_PER_SEC_SYS′ =ₑ tickspersecond′ ;ₛ
      prdlo′ =ᶠ compute_period(· OS_TICKS_PER_SEC_SYS′, ′CPU_CLK_KHZ·);ₛ
      OStimer_Init(­ ′DNUM, prdlo′,  ′0  ­);ₛ
      EXIT_CRITICAL;ₛ 
      RETURN ′0 
      }·.

(*不完整： 缺少string, longlong int, break *)
Definition OStimer_create_impl :=
      Int32 ·OStimer_create·(⌞timerid @ Int32; prdlo @ Int32u; prdhi @Int32u; mode @ Int32u; intfunc @ Int32u ; intarg @ Void∗ ⌟)··{
      ⌞
       ret @ Int32u;
       err @ Int32u;
       i @Int32;
       flag @Int32u
      ⌟; 
      
      err′ =ₑ ′0;ₛ
      ret′ =ₑ ′0;ₛ

      If ( timerid′ >ₑ ′7 &&ₑ timerid′ <ₑ ′16){
            ENTER_CRITICAL;ₛ
            OStimer_Config(­ timerid′ , prdlo′ , prdhi′, mode′, ′1 ­);ₛ
            OStimer_outConfig(-timerid′ ,′1 -);ₛ

            i′ =ₑ ′INT_NUM_MIN;ₛ
            flag′ =ₑ ′1;ₛ

            WHILE ((i′ <ₑ (′INT_NUM_MAX +ₑ ′1) &&ₑ flag′ )) {
                  If (OSIntHandler′[i′ − ′INT_NUM_MIN] ==ₑ NULL){
                        OSint_install_handler_timer(­ i′, i′, intfunc′ , intarg′,′CSL_GEM_TINT8L +ₑ (timerid′ − ′8) × ′2 ­);ₛ
                        (*缺少 break TODO *)
                        flag′ =ₑ ′0
                        (* 采用flag让其退出while*)
                  };ₛ
                  ++ i′
            };ₛ

            If (flag′){
                  err′ =ₑ ′EAGAIN;ₛ
                  EXIT_CRITICAL;ₛ
                  RETURN ′-1 
            };ₛ

            OS_timerid_used′[timerid′ − ′8] =ₑ ′1;ₛ
            EXIT_CRITICAL;ₛ
            RETURN ′0 
      };ₛ
      err′ =ₑ ′EINVAL;ₛ
      RETURN  ′-1 
      }·.


Definition OStimer_start_impl :=
      Int32 ·OStimer_start·(⌞timerid @ Int32⌟)··{
      ⌞
      err @ Int32u;
      ret @ Int32u;
      Timer_TGCR @Int32u ∗ 
      ⌟; 
      
      err′ =ₑ ′0;ₛ
      ret′ =ₑ ′0;ₛ

      (* If ( timerid′ >ₑ ′7 &&ₑ timerid′ <ₑ ′16 &&ₑ OS_timerid_used′[timerid′ − ′8] ==ₑ ′1 ) *)
      If ( timerid′ >ₑ ′7 &&ₑ timerid′ <ₑ ′16 )
      {     
            ENTER_CRITICAL;ₛ
            If (OS_timerid_used′[timerid′ − ′8] ==ₑ ′1 ){
                  Timer_TGCR′  =ₑ 〈Int32u ∗〉((__timerregs′ +ₑ ′9 ) +ₑ (timerid′ ≪ ′14 ));ₛ
                  ∗ Timer_TGCR′ =ₑ ∗ Timer_TGCR′ |ₑ ′3;ₛ
                  EXIT_CRITICAL;ₛ
                  RETURN ′0 
            };ₛ
            EXIT_CRITICAL
      };ₛ
      err′ =ₑ ′EINVAL;ₛ
      RETURN  ′-1 
      }·.

Definition OStimer_stop_impl :=
      Int32 ·OStimer_stop·(⌞timerid @ Int32⌟)··{
      ⌞
      err @ Int32u;
      ret @ Int32u;
      Timer_TGCR @Int32u ∗ 
      ⌟; 
      
      err′ =ₑ ′0;ₛ
      ret′ =ₑ ′0;ₛ

      (* If ( timerid′ >ₑ ′7 &&ₑ timerid′ <ₑ ′16 &&ₑ OS_timerid_used′[timerid′ − ′8] ==ₑ ′1 ) *)
      If ( timerid′ >ₑ ′7 &&ₑ timerid′ <ₑ ′16 )
      {     
            ENTER_CRITICAL;ₛ
            If (OS_timerid_used′[timerid′ − ′8] ==ₑ ′1 ){
                  Timer_TGCR′  =ₑ 〈Int32u ∗〉((__timerregs′ +ₑ ′9 ) +ₑ (timerid′ ≪ ′14 ));ₛ
                  ∗ Timer_TGCR′ =ₑ ∗ Timer_TGCR′ &ₑ ′4294967292;ₛ
                  EXIT_CRITICAL;ₛ
                  RETURN ′0 
            };ₛ
            EXIT_CRITICAL
      };ₛ
      err′ =ₑ ′EINVAL;ₛ
      RETURN  ′-1 
      }·.

Definition OStimer_resume_impl :=
      Int32 ·OStimer_resume·(⌞timerid @ Int32⌟)··{
      ⌞
      ⌟; 
      RETURN  ′0
      }·.

Definition OStimer_delete_impl :=
      Int32 ·OStimer_delete·(⌞timerid @ Int32⌟)··{
      ⌞
      err @ Int32u;
      ret @ Int32u
      ⌟; 
      
      err′ =ₑ ′0;ₛ
      ret′ =ₑ ′0;ₛ

      If ( timerid′ >ₑ ′7 &&ₑ timerid′ <ₑ ′16 )
      {     
            ENTER_CRITICAL;ₛ
            If (OS_timerid_used′[timerid′ − ′8] ==ₑ ′1 ){
                  OSreset_timer(­timerid′ ­);ₛ
                  OS_timerid_used′[timerid′ − ′8] =ₑ ′0;ₛ
                  EXIT_CRITICAL;ₛ
                  RETURN ′0 
            };ₛ
            EXIT_CRITICAL
      };ₛ
      err′ =ₑ ′EINVAL;ₛ
      RETURN  ′-1 
      }·.

Definition OStimer_gettime_impl :=
      Int32 ·OStimer_gettime·(⌞timerid @ Int32; cntlow @ Int32u∗ ; cnthigh @ Int32u∗ ⌟)··{
      ⌞
            err @ Int32u;
            ret @ Int32u;
            TimerRegs_CNTLO @Int32u ∗ ;
            TimerRegs_CNTHI @Int32u ∗ 
      ⌟; 
      
      err′ =ₑ ′0;ₛ
      ret′ =ₑ ′0;ₛ

      If ( timerid′ >ₑ ′7 &&ₑ timerid′ <ₑ ′16 ){
            ENTER_CRITICAL;ₛ
            If (OS_timerid_used′[timerid′ − ′8] ==ₑ ′1 ){
                  TimerRegs_CNTLO′ =ₑ NULL ;ₛ
                  TimerRegs_CNTHI′ =ₑ NULL ;ₛ

                  TimerRegs_CNTLO′ =ₑ 〈Int32u ∗〉((__timerregs′ +ₑ ′4 ) +ₑ (timerid′ × ′16384 ));ₛ 
                  TimerRegs_CNTHI′ =ₑ 〈Int32u ∗〉((__timerregs′ +ₑ ′5 ) +ₑ (timerid′ × ′16384 ));ₛ
            
                  (* (∗ value′) =ᶠ _itoll(· ∗ TimerRegs_CNTLO′ , ∗ TimerRegs_CNTHI′ ·);ₛ *)
                  ∗ cntlow′ =ₑ ∗ TimerRegs_CNTLO′ ;ₛ
                  (* OSTCBCur′→OSTCBLoc =ₑ (′__OSLoc_tmrget_getlo≪ ′4) +ₑ timerid′;ₛ *)
                  ∗ cnthigh′ =ₑ ∗ TimerRegs_CNTHI′ ;ₛ
                  (* OSTCBCur′→OSTCBLoc =ₑ ′0;ₛ *)
                  EXIT_CRITICAL;ₛ
                  RETURN ′0 
            };ₛ
            EXIT_CRITICAL
      };ₛ
      err′ =ₑ ′EINVAL;ₛ
      RETURN  ′-1 
      }·.

(* internal functions :
                  -----these funcions are all in critical region*) 
Definition OStimer_Config_impl :=
      Void ·OStimer_Config·(⌞timerid @ Int32; prdlo @ Int32u; prdhi @Int32u; mode @Int32u; enable64bit @Int32u ⌟)··{
      ⌞
            timerx @ OSTimerRegs ∗

      ⌟; 
      
      (* timerx′ =ₑ〈OSTimerRegs ∗〉(′TIMER_BASE  +ₑ  (timerid′ ≪ ′16 ) ) ;ₛ *)
      timerx′ =ₑ〈OSTimerRegs ∗〉(__timerregs′  +ₑ  (timerid′ ≪ ′14 ) ) ;ₛ
      timerx′ → OSPRDLO =ₑ prdlo′;ₛ
      timerx′ → OSPRDHI =ₑ prdhi′;ₛ
      timerx′ → OSCNTLO =ₑ ′0;ₛ
      timerx′ → OSCNTHI =ₑ ′0;ₛ

      IF ( mode′ ){
            timerx′ → OSTCRreg =ₑ ′128
      } ELSE{ 
            timerx′ → OSTCRreg =ₑ ′64
      };ₛ
      IF ( enable64bit′ ){
            timerx′ → OSTGCR =ₑ ′0
      } ELSE{ 
            timerx′ → OSTGCR =ₑ ′4
      };ₛ
      RETURN
      }·.
      
Definition OStimer_outConfig_impl :=
      Void ·OStimer_outConfig·(⌞timerid @ Int32; outputmode @Int32u ⌟)··{
      ⌞
      TimerRegs_TCR @ Int32u ∗

      ⌟; 
      
      (* TimerRegs_TCR ′ =ₑ〈Int32u ∗〉(′TCR_REG  +ₑ (timerid′ ≪ ′16 ) ) ;ₛ *)
      TimerRegs_TCR ′ =ₑ〈Int32u ∗〉((__timerregs′ +ₑ ′8 ) +ₑ (timerid′ ≪ ′14 ) ) ;ₛ
      IF ( outputmode′ ){
            ∗TimerRegs_TCR′ =ₑ ∗TimerRegs_TCR′ |ₑ  ′8
      } ELSE{ 
            ∗TimerRegs_TCR′ =ₑ ∗TimerRegs_TCR′ &ₑ  ′4294967287
      };ₛ
      RETURN
      }·.

Definition OSreset_timer_impl :=
      Void ·OSreset_timer·(⌞timerid @ Int32 ⌟)··{
      ⌞
      TimerRegs_TGCR @ Int32u ∗ ;
      TimerRegs_TCR @ Int32u ∗

      ⌟; 

      TimerRegs_TGCR′ =ₑ NULL ;ₛ
      TimerRegs_TCR′ =ₑ NULL ;ₛ

      (* TimerRegs_TGCR ′ =ₑ〈Int32u ∗〉(′timerRegs0_TGCR +ₑ (timerid′ × ′65536 ) ) ;ₛ
      TimerRegs_TCR ′ =ₑ〈Int32u ∗〉(′timerRegs0_TCR +ₑ (timerid′ × ′65536 ) ) ;ₛ *)
      TimerRegs_TGCR ′ =ₑ〈Int32u ∗〉((__timerregs′ +ₑ ′9 ) +ₑ (timerid′ × ′16384 ) ) ;ₛ
      TimerRegs_TCR ′ =ₑ〈Int32u ∗〉((__timerregs′ +ₑ ′8 ) +ₑ (timerid′ × ′16384 ) ) ;ₛ

      If ( ∗ TimerRegs_TGCR ′){
            ∗TimerRegs_TGCR′ =ₑ  ′0;ₛ
            ∗TimerRegs_TCR′ =ₑ  ′0
      };ₛ
      RETURN
      }·.

Definition OStimer_Init_impl :=
      Void ·OStimer_Init·(⌞timerid @ Int32; prdlo @ Int32 ; prdhi @ Int32  ⌟)··{
      ⌞
      TimerRegs_CNTLO @ Int32u ∗ ;
      TimerRegs_CNTHI @ Int32u ∗ ;
      TimerRegs_PRDLO @ Int32u ∗ ;
      TimerRegs_PRDHI @ Int32u ∗ ;
      TimerRegs_EMUMGT_CLKSPD @ Int32u ∗ ;
      TimerRegs_TGCR @ Int32u ∗ ;
      TimerRegs_TCR @ Int32u ∗ 
      ⌟; 

      TimerRegs_CNTLO ′ =ₑ NULL ;ₛ
      TimerRegs_CNTHI ′ =ₑ NULL ;ₛ
      TimerRegs_PRDLO ′ =ₑ NULL ;ₛ
      TimerRegs_PRDHI ′ =ₑ NULL ;ₛ
      TimerRegs_EMUMGT_CLKSPD ′ =ₑ NULL ;ₛ
      TimerRegs_TGCR′ =ₑ NULL ;ₛ
      TimerRegs_TCR′ =ₑ NULL ;ₛ

      TimerRegs_CNTLO ′ =ₑ〈Int32u ∗〉((__timerregs′ +ₑ ′4 ) +ₑ (timerid′ × ′16384 ) ) ;ₛ
      TimerRegs_CNTHI ′ =ₑ〈Int32u ∗〉((__timerregs′ +ₑ ′5 ) +ₑ (timerid′ × ′16384 ) ) ;ₛ
      TimerRegs_PRDLO ′ =ₑ〈Int32u ∗〉((__timerregs′ +ₑ ′6 ) +ₑ (timerid′ × ′16384 ) ) ;ₛ
      TimerRegs_PRDHI ′ =ₑ〈Int32u ∗〉((__timerregs′ +ₑ ′7 ) +ₑ (timerid′ × ′16384 ) ) ;ₛ
      TimerRegs_EMUMGT_CLKSPD ′ =ₑ〈Int32u ∗〉((__timerregs′ +ₑ ′1 ) +ₑ (timerid′ × ′16384 ) ) ;ₛ
      TimerRegs_TGCR ′ =ₑ〈Int32u ∗〉((__timerregs′ +ₑ ′9 ) +ₑ (timerid′ × ′16384 ) ) ;ₛ
      TimerRegs_TCR ′ =ₑ〈Int32u ∗〉((__timerregs′ +ₑ ′8 ) +ₑ (timerid′ × ′16384 ) ) ;ₛ
      OSreset_timer(­timerid′ ­);ₛ
      ∗TimerRegs_CNTLO′ =ₑ  ′0;ₛ
      ∗TimerRegs_CNTHI′ =ₑ  ′0;ₛ
      ∗TimerRegs_PRDLO′ =ₑ  prdlo′;ₛ
      ∗TimerRegs_PRDHI′ =ₑ  prdhi′;ₛ
      ∗TimerRegs_TGCR′=ₑ
			(* /*Select 64-bit general timer mode*/ *)
			(′ CSL_TMR_TIMMODE_GPT ≪ ′CSL_TMR_TGCR_TIMMODE_SHIFT)
			(* /*Remove the timer from reset*/ *)
			|ₑ (′ CSL_TMR_TGCR_TIMLORS_RESET_OFF ≪ ′ CSL_TMR_TGCR_TIMLORS_SHIFT)
			|ₑ (′ CSL_TMR_TGCR_TIMHIRS_RESET_OFF ≪ ′ CSL_TMR_TGCR_TIMHIRS_SHIFT);ₛ
      ∗TimerRegs_EMUMGT_CLKSPD′ =ₑ ((∗TimerRegs_EMUMGT_CLKSPD′)&ₑ
			(′CSL_TMR_EMUMGT_CLKSPD_MASK ));ₛ
      ∗TimerRegs_TCR′=ₑ
			(′ CSL_TMR_CLOCK_INP_NOGATE≪ ′CSL_TMR_TCR_TIEN_LO_SHIFT   )
			|ₑ(′ CSL_TMR_CLKSRC_INTERNAL≪ ′CSL_TMR_TCR_CLKSRC_LO_SHIFT )
			|ₑ(′CSL_TMR_ENAMODE_CONT≪′CSL_TMR_TCR_ENAMODE_LO_SHIFT)
			|ₑ(′0≪ ′CSL_TMR_TCR_PWID_LO_SHIFT   )
			(* /*select clock mode*/ *)
			|ₑ(′CSL_TMR_CP_CLOCK≪′CSL_TMR_TCR_CP_LO_SHIFT     )
			|ₑ(′CSL_TMR_INVINP_UNINVERTED≪′CSL_TMR_TCR_INVINP_LO_SHIFT )
			|ₑ(′CSL_TMR_INVOUTP_UNINVERTED≪′CSL_TMR_TCR_INVOUTP_LO_SHIFT)
			|ₑ(′0≪′CSL_TMR_TCR_TSTAT_LO_SHIFT  );ₛ
      RETURN
      }·.



Close Scope code_scope.
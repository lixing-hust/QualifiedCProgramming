Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Open Scope code_scope.

Definition partitionSysInit_impl := 
Void ·partitionSysInit·(⌞⌟)··{
                   ⌞ ⌟;
 
                    ENTER_CRITICAL;ₛ
                    ksDomScheduleIdx′ =ₑ   ′0 ;ₛ
                    os_code_defs.isCoreBoot′ =ₑ   ′0 ;ₛ
                    ksDomainTime′ =ₑ ( efield(ksDomSchedule′[ksDomScheduleIdx′])dscd_length);ₛ
                    isChangePartion′ =ₑ   ′0;ₛ
                    ksLastDomain′  =ₑ (′-1);ₛ
                    ksCurDomain′ =ₑ (efield (ksDomSchedule′[ksDomScheduleIdx′]) dscd_domain);ₛ
                    OSSystemSP′=ₑ   (&ₐ ( systemStck′[′(( SYS_STK_SIZE )- 1) ] )) &  (∼′7)  ;ₛ 
                   EXIT_CRITICAL;ₛ
                   RETURN

}· .

Definition nextDomain_impl :=
 Void ·nextDomain·(⌞ ⌟)··{
 
       ⌞ ⌟;

       ENTER_CRITICAL;ₛ
       ++ ksDomScheduleIdx′;ₛ
       If (ksDomScheduleIdx′ ≥ ksDomScheduleLength′) {
            ksDomScheduleIdx′ =ₑ ′0
       };ₛ
       ksLastDomain′ =ₑ ksCurDomain′;ₛ
       ksCurDomain′ =ₑ (efield (ksDomSchedule′[ksDomScheduleIdx′]) dscd_domain);ₛ
       ksDomainTime′ =ₑ (efield (ksDomSchedule′[ksDomScheduleIdx′]) dscd_length);ₛ
       isChangePartion′ =ₑ ′1;ₛ
       EXIT_CRITICAL;ₛ
       RETURN

 }·.

Definition getPartitionID_impl := 
Int8u ·getPartitionID·(⌞⌟)··{
       ⌞
       ksdid      @ dom_t;
       ksdid1   @ Int8u
        ⌟;

       ENTER_CRITICAL;ₛ
       ksdid′   =ₑ ksCurDomain′;ₛ
       EXIT_CRITICAL;ₛ
       ENTER_CRITICAL;ₛ
       ksdid1′   =ₑ  efield (ksDomains′[ksdid′]) dom_t_ID;ₛ
       EXIT_CRITICAL;ₛ
       (*  RETURN  ksDomains[ksCurDomain].ID; *)
       RETURN ksdid1′

}· .

Close Scope code_scope.



Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Open Scope code_scope.

(* SUPERVISOR_MODE_EN > 0 *)
Definition switchDomain_impl := 
    Void ·switchDomain·(⌞mpaxh @ XMC_XMPAXH∗ ;
                                                   mpaxl @ XMC_XMPAXL∗ ;
                                                   ses_mpaxh  @ MSMC_SESMPAXH∗ ;
                                                   ses_mpaxl  @ MSMC_SESMPAXL∗ ;
                                                   sms_mpaxh @ MSMC_SMSMPAXH∗ ;
                                                   sms_mpaxl @ MSMC_SMSMPAXL∗⌟)·
·{
        ⌞
        index @ Int32u;
        paddress @ Int32u;
        coreNum @ Int32u;
        segSize @ Int8u
        ⌟;
         
        index′ =ₑ ′0;ₛ
        paddress′ =ₑ ′0;ₛ
        coreNum′ =ₑ ′DNUM;ₛ
        If (ksLastDomain′ !=ₑ ksCurDomain′){
            IF (ksCurDomain′  !=ₑ (′-1)){
                index′ =ₑ ′MPAXSHIPARTIONSTKCUR ;ₛ             
                mpaxh′→mpaxh_segSize  =ₑ ′12 ;ₛ 
                mpaxh′→mpaxh_bAddr  =ₑ (〈Int32u〉(&ₐ(RootTaskStk′[ksDomains′[ksCurDomain′]..dom_t_ID]))) ≫ ′12;ₛ 
                CSL_XMC_setXMPAXH(index′ ,    mpaxh′);ₛ 

                sms_mpaxh′→smsmpaxh_segSz  =ₑ ′12 ;ₛ 
                sms_mpaxh′→smsmpaxh_bAddr  =ₑ (〈Int32u〉(&ₐ(RootTaskStk′[ksDomains′[ksCurDomain′]..dom_t_ID]))) ≫ ′12 ;ₛ 
                CSL_MSMC_setSMSMPAXH(coreNum′ ,index′,   sms_mpaxh′);ₛ

                ses_mpaxh′→sesmpaxh_segSz  =ₑ ′12 ;ₛ 
                ses_mpaxh′→sesmpaxh_bAddr  =ₑ (〈Int32u〉(&ₐ(RootTaskStk′[ksDomains′[ksCurDomain′]..dom_t_ID]))) ≫ ′12;ₛ 
                CSL_MSMC_setSESMPAXH(coreNum′ , index′ ,    ses_mpaxh′);ₛ

                paddress′ =ₑ 〈Int32u〉(&ₐ(RootTaskStk′[ksDomains′[ksCurDomain′]..dom_t_ID]));ₛ 
                IF (paddress′  ≥ ′0x80000000){
                    paddress′ =ₑ ((paddress′ − ′0x80000000) ≫ ′12) |ₑ ′0x800000
                }
                ELSE{
                    paddress′ =ₑ paddress′ ≫ ′12
                };ₛ 
                mpaxl′→mpaxl_ux =ₑ ′1;ₛ 
                mpaxl′→mpaxl_uw =ₑ ′1;ₛ 
                mpaxl′→mpaxl_ur =ₑ ′1;ₛ 
                mpaxl′→mpaxl_sx =ₑ ′1;ₛ 
                mpaxl′→mpaxl_sw =ₑ ′1;ₛ 
                mpaxl′→mpaxl_sr =ₑ ′1;ₛ 
                mpaxl′→mpaxl_rAddr =ₑ paddress′;ₛ 
                CSL_XMC_setXMPAXL(index′ ,    mpaxl′);ₛ 

                sms_mpaxl′→smsmpaxl_ux =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_uw =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_ur =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_sx =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_sw =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_sr =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_raddr =ₑ paddress′;ₛ 
                CSL_MSMC_setSMSMPAXL(coreNum′,index′,  sms_mpaxl′);ₛ 

                ses_mpaxl′→sesmpaxl_ux=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_uw=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_ur=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_sx=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_sw=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_sr=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_raddr=ₑ  paddress′;ₛ
                CSL_MSMC_setSESMPAXL(coreNum′,index′,  ses_mpaxl′);ₛ 

                index′ =ₑ ′MPAXSHIPARTIONCUR ;ₛ 
                mpaxh′→mpaxh_segSize  =ₑ ksDomains′[ksCurDomain′]..dom_t_size ;ₛ 
                mpaxh′→mpaxh_bAddr  =ₑ  (ksDomains′[ksCurDomain′]..dom_t_vAddress) ≫ ′12 ;ₛ  
                CSL_XMC_setXMPAXH(index′ ,    mpaxh′);ₛ 

                sms_mpaxh′→smsmpaxh_segSz  =ₑ  ksDomains′[ksCurDomain′]..dom_t_size ;ₛ 
                sms_mpaxh′→smsmpaxh_bAddr  =ₑ (ksDomains′[ksCurDomain′]..dom_t_vAddress) ≫ ′12 ;ₛ  
                CSL_MSMC_setSMSMPAXH(coreNum′ ,index′,   sms_mpaxh′);ₛ 

                ses_mpaxh′→sesmpaxh_segSz  =ₑ ksDomains′[ksCurDomain′]..dom_t_size ;ₛ 
                ses_mpaxh′→sesmpaxh_bAddr  =ₑ (ksDomains′[ksCurDomain′]..dom_t_vAddress) ≫ ′12 ;ₛ 
                CSL_MSMC_setSESMPAXH(coreNum′ , index′ ,    ses_mpaxh′);ₛ 
    
                paddress′ =ₑ ksDomains′[ksCurDomain′]..dom_t_pAddress;ₛ 
                IF (paddress′  ≥ ′0x80000000){
                    paddress′ =ₑ ((paddress′ − ′0x80000000) ≫ ′12) |ₑ ′0x800000
                }
                ELSE{
                    paddress′ =ₑ paddress′ ≫ ′12
                };ₛ 

                mpaxl′→mpaxl_ux =ₑ ′1;ₛ 
                mpaxl′→mpaxl_uw =ₑ ′1;ₛ 
                mpaxl′→mpaxl_ur =ₑ ′1;ₛ 
                mpaxl′→mpaxl_sx =ₑ ′1;ₛ 
                mpaxl′→mpaxl_sw =ₑ ′1;ₛ 
                mpaxl′→mpaxl_sr =ₑ ′1;ₛ 
                mpaxl′→mpaxl_rAddr =ₑ  paddress′ ;ₛ 
                CSL_XMC_setXMPAXL(index′ ,    mpaxl′);ₛ 

                sms_mpaxl′→smsmpaxl_ux =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_uw =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_ur =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_sx =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_sw =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_sr =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_raddr =ₑ paddress′ ;ₛ 
                CSL_MSMC_setSMSMPAXL(coreNum′,index′,  sms_mpaxl′);ₛ 

                ses_mpaxl′→sesmpaxl_ux=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_uw=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_ur=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_sx=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_sw=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_sr=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_raddr=ₑ  paddress′ ;ₛ 
                CSL_MSMC_setSESMPAXL(coreNum′,index′,  ses_mpaxl′)
                }
                ELSE{            
                index′ =ₑ ′MPAXSHIPARTIONCUR ;ₛ 

                mpaxh′→mpaxh_segSize  =ₑ ′0x00;ₛ 
                mpaxh′→mpaxh_bAddr  =ₑ   ′0x00 ;ₛ  
                CSL_XMC_setXMPAXH(index′ ,    mpaxh′);ₛ 

                sms_mpaxh′→smsmpaxh_segSz  =ₑ   ′0x00;ₛ  
                sms_mpaxh′→smsmpaxh_bAddr  =ₑ   ′0x00;ₛ  
                CSL_MSMC_setSMSMPAXH(coreNum′ ,index′,   sms_mpaxh′);ₛ 

                ses_mpaxh′→sesmpaxh_segSz  =ₑ  ′0x00;ₛ   
                ses_mpaxh′→sesmpaxh_bAddr  =ₑ   ′0x00;ₛ    
                CSL_MSMC_setSESMPAXH(coreNum′ , index′ ,    ses_mpaxh′);ₛ
            
                mpaxl′→mpaxl_ux =ₑ ′0;ₛ 
                mpaxl′→mpaxl_uw =ₑ ′0;ₛ 
                mpaxl′→mpaxl_ur =ₑ ′0;ₛ 

                mpaxl′→mpaxl_sx =ₑ ′1;ₛ 
                mpaxl′→mpaxl_sw =ₑ ′1;ₛ 
                mpaxl′→mpaxl_sr =ₑ ′1;ₛ 

                mpaxl′→mpaxl_rAddr =ₑ ′0x00 ≫ ′12 ;ₛ  
                CSL_XMC_setXMPAXL(index′ ,    mpaxl′);ₛ 

                sms_mpaxl′→smsmpaxl_ux =ₑ ′0;ₛ 
                sms_mpaxl′→smsmpaxl_uw =ₑ ′0;ₛ 
                sms_mpaxl′→smsmpaxl_ur =ₑ ′0;ₛ 

                sms_mpaxl′→smsmpaxl_sx =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_sw =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_sr =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_raddr =ₑ   ′0x00 ≫ ′12 ;ₛ  
                CSL_MSMC_setSMSMPAXL(coreNum′,index′,  sms_mpaxl′);ₛ  

                ses_mpaxl′→sesmpaxl_ux=ₑ ′0;ₛ 
                ses_mpaxl′→sesmpaxl_uw=ₑ ′0;ₛ 
                ses_mpaxl′→sesmpaxl_ur=ₑ ′0;ₛ 

                ses_mpaxl′→sesmpaxl_sx=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_sw=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_sr=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_raddr=ₑ    ′0x00 ≫ ′12 ;ₛ 
                CSL_MSMC_setSESMPAXL(coreNum′,index′,  ses_mpaxl′)
                }
            } ;ₛ

     RETURN

}· .

(* SUPERVISOR_MODE_EN = 0 *)
Definition switchDomain_impl' := 
    Void ·switchDomain'·(⌞mpaxh @ XMC_XMPAXH∗ ;
                                                   mpaxl @ XMC_XMPAXL∗ ;
                                                   ses_mpaxh  @ MSMC_SESMPAXH∗ ;
                                                   ses_mpaxl  @ MSMC_SESMPAXL∗ ;
                                                   sms_mpaxh @ MSMC_SMSMPAXH∗ ;
                                                   sms_mpaxl @ MSMC_SMSMPAXL∗⌟)·
·{
        ⌞
        index @ Int32u;
        paddress @ Int32u;
        coreNum @ Int32u;
        segSize @ Int8u
        ⌟;
         
        index′ =ₑ ′0;ₛ
        paddress′ =ₑ ′0;ₛ
        coreNum′ =ₑ ′DNUM;ₛ
        If (ksLastDomain′ !=ₑ ksCurDomain′){
            IF (ksCurDomain′  !=ₑ (′-1)){
                index′ =ₑ ′MPAXSHIPARTIONSTKCUR ;ₛ             
                mpaxh′→mpaxh_segSize  =ₑ ′12 ;ₛ 
                mpaxh′→mpaxh_bAddr  =ₑ (〈Int32u〉(&ₐ(RootTaskStk′[ksDomains′[ksCurDomain′]..dom_t_ID]))) ≫ ′12;ₛ 
                CSL_XMC_setXMPAXH(index′ ,    mpaxh′);ₛ 

                sms_mpaxh′→smsmpaxh_segSz  =ₑ ′12 ;ₛ 
                sms_mpaxh′→smsmpaxh_bAddr  =ₑ (〈Int32u〉(&ₐ(RootTaskStk′[ksDomains′[ksCurDomain′]..dom_t_ID]))) ≫ ′12 ;ₛ 
                CSL_MSMC_setSMSMPAXH(coreNum′ ,index′,   sms_mpaxh′);ₛ

                ses_mpaxh′→sesmpaxh_segSz  =ₑ ′12 ;ₛ 
                ses_mpaxh′→sesmpaxh_bAddr  =ₑ (〈Int32u〉(&ₐ(RootTaskStk′[ksDomains′[ksCurDomain′]..dom_t_ID]))) ≫ ′12;ₛ 
                CSL_MSMC_setSESMPAXH(coreNum′ , index′ ,    ses_mpaxh′);ₛ

                paddress′ =ₑ 〈Int32u〉(&ₐ(RootTaskStk′[ksDomains′[ksCurDomain′]..dom_t_ID]));ₛ 
                IF (paddress′  ≥ ′0x80000000){
                    paddress′ =ₑ ((paddress′ − ′0x80000000) ≫ ′12) |ₑ ′0x800000
                }
                ELSE{
                    paddress′ =ₑ paddress′ ≫ ′12
                };ₛ 
                mpaxl′→mpaxl_ux =ₑ ′1;ₛ 
                mpaxl′→mpaxl_uw =ₑ ′1;ₛ 
                mpaxl′→mpaxl_ur =ₑ ′1;ₛ 
                mpaxl′→mpaxl_sx =ₑ ′1;ₛ 
                mpaxl′→mpaxl_sw =ₑ ′1;ₛ 
                mpaxl′→mpaxl_sr =ₑ ′1;ₛ 
                mpaxl′→mpaxl_rAddr =ₑ paddress′;ₛ 
                CSL_XMC_setXMPAXL(index′ ,    mpaxl′);ₛ 

                sms_mpaxl′→smsmpaxl_ux =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_uw =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_ur =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_sx =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_sw =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_sr =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_raddr =ₑ paddress′;ₛ 
                CSL_MSMC_setSMSMPAXL(coreNum′,index′,  sms_mpaxl′);ₛ 

                ses_mpaxl′→sesmpaxl_ux=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_uw=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_ur=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_sx=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_sw=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_sr=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_raddr=ₑ  paddress′;ₛ
                CSL_MSMC_setSESMPAXL(coreNum′,index′,  ses_mpaxl′);ₛ 

                index′ =ₑ ′MPAXSHIPARTIONCUR ;ₛ 
                mpaxh′→mpaxh_segSize  =ₑ ksDomains′[ksCurDomain′]..dom_t_size ;ₛ 
                mpaxh′→mpaxh_bAddr  =ₑ  (ksDomains′[ksCurDomain′]..dom_t_vAddress) ≫ ′12 ;ₛ  
                CSL_XMC_setXMPAXH(index′ ,    mpaxh′);ₛ 

                sms_mpaxh′→smsmpaxh_segSz  =ₑ  ksDomains′[ksCurDomain′]..dom_t_size ;ₛ 
                sms_mpaxh′→smsmpaxh_bAddr  =ₑ (ksDomains′[ksCurDomain′]..dom_t_vAddress) ≫ ′12 ;ₛ  
                CSL_MSMC_setSMSMPAXH(coreNum′ ,index′,   sms_mpaxh′);ₛ 

                ses_mpaxh′→sesmpaxh_segSz  =ₑ ksDomains′[ksCurDomain′]..dom_t_size ;ₛ 
                ses_mpaxh′→sesmpaxh_bAddr  =ₑ (ksDomains′[ksCurDomain′]..dom_t_vAddress) ≫ ′12 ;ₛ 
                CSL_MSMC_setSESMPAXH(coreNum′ , index′ ,    ses_mpaxh′);ₛ 
    
                paddress′ =ₑ ksDomains′[ksCurDomain′]..dom_t_pAddress;ₛ 
                IF (paddress′  ≥ ′0x80000000){
                    paddress′ =ₑ ((paddress′ − ′0x80000000) ≫ ′12) |ₑ ′0x800000
                }
                ELSE{
                    paddress′ =ₑ paddress′ ≫ ′12
                };ₛ 

                mpaxl′→mpaxl_ux =ₑ ′1;ₛ 
                mpaxl′→mpaxl_uw =ₑ ′1;ₛ 
                mpaxl′→mpaxl_ur =ₑ ′1;ₛ 
                mpaxl′→mpaxl_sx =ₑ ′1;ₛ 
                mpaxl′→mpaxl_sw =ₑ ′1;ₛ 
                mpaxl′→mpaxl_sr =ₑ ′1;ₛ 
                mpaxl′→mpaxl_rAddr =ₑ  paddress′ ;ₛ 
                CSL_XMC_setXMPAXL(index′ ,    mpaxl′);ₛ 

                sms_mpaxl′→smsmpaxl_ux =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_uw =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_ur =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_sx =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_sw =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_sr =ₑ ′1;ₛ 
                sms_mpaxl′→smsmpaxl_raddr =ₑ paddress′ ;ₛ 
                CSL_MSMC_setSMSMPAXL(coreNum′,index′,  sms_mpaxl′);ₛ 

                ses_mpaxl′→sesmpaxl_ux=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_uw=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_ur=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_sx=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_sw=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_sr=ₑ ′1;ₛ 
                ses_mpaxl′→sesmpaxl_raddr=ₑ  paddress′ ;ₛ 
                CSL_MSMC_setSESMPAXL(coreNum′,index′,  ses_mpaxl′)
                }
                ELSE{            
                index′ =ₑ ′MPAXSHIPARTIONCUR ;ₛ 

                mpaxh′→mpaxh_segSize  =ₑ ′0x00;ₛ 
                mpaxh′→mpaxh_bAddr  =ₑ   ′0x00 ;ₛ  
                CSL_XMC_setXMPAXH(index′ ,    mpaxh′);ₛ 

                sms_mpaxh′→smsmpaxh_segSz  =ₑ   ′0x00;ₛ  
                sms_mpaxh′→smsmpaxh_bAddr  =ₑ   ′0x00;ₛ  
                CSL_MSMC_setSMSMPAXH(coreNum′ ,index′,   sms_mpaxh′);ₛ 

                ses_mpaxh′→sesmpaxh_segSz  =ₑ  ′0x00;ₛ   
                ses_mpaxh′→sesmpaxh_bAddr  =ₑ   ′0x00;ₛ    
                CSL_MSMC_setSESMPAXH(coreNum′ , index′ ,    ses_mpaxh′);ₛ
            
                mpaxl′→mpaxl_ux =ₑ ′0;ₛ 
                mpaxl′→mpaxl_uw =ₑ ′0;ₛ 
                mpaxl′→mpaxl_ur =ₑ ′0;ₛ 

                mpaxl′→mpaxl_sx =ₑ ′0;ₛ 
                mpaxl′→mpaxl_sw =ₑ ′0;ₛ 
                mpaxl′→mpaxl_sr =ₑ ′0;ₛ 

                mpaxl′→mpaxl_rAddr =ₑ ′0x00 ≫ ′12 ;ₛ  
                CSL_XMC_setXMPAXL(index′ ,    mpaxl′);ₛ 

                sms_mpaxl′→smsmpaxl_ux =ₑ ′0;ₛ 
                sms_mpaxl′→smsmpaxl_uw =ₑ ′0;ₛ 
                sms_mpaxl′→smsmpaxl_ur =ₑ ′0;ₛ 

                sms_mpaxl′→smsmpaxl_sx =ₑ ′0;ₛ 
                sms_mpaxl′→smsmpaxl_sw =ₑ ′0;ₛ 
                sms_mpaxl′→smsmpaxl_sr =ₑ ′0;ₛ 
                sms_mpaxl′→smsmpaxl_raddr =ₑ   ′0x00 ≫ ′12 ;ₛ  
                CSL_MSMC_setSMSMPAXL(coreNum′,index′,  sms_mpaxl′);ₛ  

                ses_mpaxl′→sesmpaxl_ux=ₑ ′0;ₛ 
                ses_mpaxl′→sesmpaxl_uw=ₑ ′0;ₛ 
                ses_mpaxl′→sesmpaxl_ur=ₑ ′0;ₛ 

                ses_mpaxl′→sesmpaxl_sx=ₑ ′0;ₛ 
                ses_mpaxl′→sesmpaxl_sw=ₑ ′0;ₛ 
                ses_mpaxl′→sesmpaxl_sr=ₑ ′0;ₛ 
                ses_mpaxl′→sesmpaxl_raddr=ₑ    ′0x00 ≫ ′12 ;ₛ 
                CSL_MSMC_setSESMPAXL(coreNum′,index′,  ses_mpaxl′)
                }
            } ;ₛ

     RETURN

}· .

Definition initDefaultMPAX_impl:= 
    Void ·initDefaultMPAX·(⌞mpaxl @ XMC_XMPAXL∗ ; sms_mpaxl @ MSMC_SMSMPAXL∗ ; ses_mpaxl @ MSMC_SESMPAXL∗ ⌟)··{
        ⌞
            corenum @ Int32u;
            index @ Int32u⌟;
         index′ =ₑ ′0;ₛ
        corenum′ =ₑ ′DNUM;ₛ

        (* WHILE (index′ <ₑ ′2) {
          CSL_XMC_getXMPAXL(index′, mpaxl′);ₛ
          mpaxl′→mpaxl_ux =ₑ ′0;ₛ
          mpaxl′→mpaxl_uw =ₑ ′0;ₛ
          mpaxl′→mpaxl_ur =ₑ ′0;ₛ
          mpaxl′→mpaxl_sx =ₑ ′1;ₛ
          mpaxl′→mpaxl_sw =ₑ ′1;ₛ
          mpaxl′→mpaxl_sr =ₑ ′1;ₛ
          CSL_XMC_setXMPAXL(index′, mpaxl′);ₛ
          ++ index′
        };ₛ *)

        index′ =ₑ ′0;ₛ
        CSL_XMC_getXMPAXL(index′, mpaxl′);ₛ
        mpaxl′→mpaxl_ux =ₑ ′0;ₛ
        mpaxl′→mpaxl_uw =ₑ ′0;ₛ
        mpaxl′→mpaxl_ur =ₑ ′0;ₛ
        mpaxl′→mpaxl_sx =ₑ ′1;ₛ
        mpaxl′→mpaxl_sw =ₑ ′1;ₛ
        mpaxl′→mpaxl_sr =ₑ ′1;ₛ
        CSL_XMC_setXMPAXL(index′, mpaxl′);ₛ

        index′ =ₑ ′1;ₛ
        CSL_XMC_getXMPAXL(index′, mpaxl′);ₛ
        mpaxl′→mpaxl_ux =ₑ ′0;ₛ
        mpaxl′→mpaxl_uw =ₑ ′0;ₛ
        mpaxl′→mpaxl_ur =ₑ ′0;ₛ
        mpaxl′→mpaxl_sx =ₑ ′1;ₛ
        mpaxl′→mpaxl_sw =ₑ ′1;ₛ
        mpaxl′→mpaxl_sr =ₑ ′1;ₛ
        CSL_XMC_setXMPAXL(index′, mpaxl′);ₛ

        index′ =ₑ ′0;ₛ
        CSL_MSMC_getSMSMPAXL (corenum′, index′, sms_mpaxl′);ₛ
        sms_mpaxl′→smsmpaxl_ux =ₑ ′0;ₛ
        sms_mpaxl′→smsmpaxl_uw =ₑ ′0;ₛ
        sms_mpaxl′→smsmpaxl_ur =ₑ ′0;ₛ
        sms_mpaxl′→smsmpaxl_sx =ₑ ′1;ₛ
        sms_mpaxl′→smsmpaxl_sw =ₑ ′1;ₛ
        sms_mpaxl′→smsmpaxl_sr =ₑ ′1;ₛ
        CSL_MSMC_setSMSMPAXL (corenum′, index′, sms_mpaxl′);ₛ

        CSL_MSMC_getSESMPAXL (corenum′, index′, ses_mpaxl′);ₛ
        ses_mpaxl′→sesmpaxl_ux =ₑ ′0;ₛ
        ses_mpaxl′→sesmpaxl_uw =ₑ ′0;ₛ
        ses_mpaxl′→sesmpaxl_ur =ₑ ′0;ₛ
        ses_mpaxl′→sesmpaxl_sx =ₑ ′1;ₛ
        ses_mpaxl′→sesmpaxl_sw =ₑ ′1;ₛ
        ses_mpaxl′→sesmpaxl_sr =ₑ ′1;ₛ
        CSL_MSMC_setSESMPAXL (corenum′, index′, ses_mpaxl′);ₛ
        RETURN
    }·.

Definition initMPAX_impl := 
    Void ·initMPAX·(⌞ mpaxh @ XMC_XMPAXH∗ ;
                                          mpaxl @ XMC_XMPAXL∗ ;
                                          ses_mpaxh  @ MSMC_SESMPAXH∗ ;
                                          ses_mpaxl  @ MSMC_SESMPAXL∗ ;
                                          sms_mpaxh @ MSMC_SMSMPAXH∗ ;
                                          sms_mpaxl @ MSMC_SMSMPAXL∗ ⌟)·
·{
        ⌞
        index @ Int32u;
        paddress @ Int32u;
        vaddress @ Int32u;
        coreNum @ Int32u;
        segSize @ Int8u     
        ⌟;

        index′ =ₑ ′0;ₛ
        paddress′ =ₑ ′0;ₛ
        vaddress′ =ₑ ′0;ₛ
        segSize′ =ₑ ′0;ₛ
        coreNum′ =ₑ ′DNUM;ₛ

        initDefaultMPAX (­mpaxl ′, sms_mpaxl ′, ses_mpaxl ′­);ₛ
        If (ksCurDomain′ !=ₑ (′-1)){
            index′ =ₑ ′MPAXSHIPARTIONSTKCUR ;ₛ             
            mpaxh′→mpaxh_segSize  =ₑ ′12 ;ₛ 
            mpaxh′→mpaxh_bAddr  =ₑ (〈Int32u〉(&ₐ(RootTaskStk′[ksDomains′[ksCurDomain′]..dom_t_ID]))) ≫ ′12;ₛ 
            CSL_XMC_setXMPAXH(index′ ,   mpaxh′);ₛ 

            sms_mpaxh′→smsmpaxh_segSz  =ₑ ′12 ;ₛ 
            sms_mpaxh′→smsmpaxh_bAddr  =ₑ (〈Int32u〉(&ₐ(RootTaskStk′[ksDomains′[ksCurDomain′]..dom_t_ID]))) ≫ ′12 ;ₛ 
            CSL_MSMC_setSMSMPAXH(coreNum′ ,index′ ,    sms_mpaxh′);ₛ

            ses_mpaxh′→sesmpaxh_segSz  =ₑ ′12 ;ₛ 
            ses_mpaxh′→sesmpaxh_bAddr  =ₑ (〈Int32u〉(&ₐ(RootTaskStk′[ksDomains′[ksCurDomain′]..dom_t_ID]))) ≫ ′12;ₛ 
            CSL_MSMC_setSESMPAXH(coreNum′ ,index′ ,    ses_mpaxh′);ₛ
            paddress′ =ₑ 〈Int32u〉(&ₐ(RootTaskStk′[ksDomains′[ksCurDomain′]..dom_t_ID]));ₛ 
            IF (paddress′  ≥ ′0x80000000){
                paddress′ =ₑ ((paddress′ − ′0x80000000) ≫ ′12) |ₑ ′0x800000
            }
            ELSE{
                paddress′ =ₑ paddress′ ≫ ′12
            };ₛ 
            mpaxl′→mpaxl_ux =ₑ ′1;ₛ 
            mpaxl′→mpaxl_uw =ₑ ′1;ₛ 
            mpaxl′→mpaxl_ur =ₑ ′1;ₛ 
            mpaxl′→mpaxl_sx =ₑ ′1;ₛ 
            mpaxl′→mpaxl_sw =ₑ ′1;ₛ 
            mpaxl′→mpaxl_sr =ₑ ′1;ₛ 
            mpaxl′→mpaxl_rAddr =ₑ paddress′;ₛ 
            CSL_XMC_setXMPAXL(index′ ,   mpaxl′);ₛ 

            sms_mpaxl′→smsmpaxl_ux =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_uw =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_ur =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_sx =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_sw =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_sr =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_raddr =ₑ paddress′;ₛ 
            CSL_MSMC_setSMSMPAXL(coreNum′,index′,   sms_mpaxl′);ₛ 

            ses_mpaxl′→sesmpaxl_ux=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_uw=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_ur=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_sx=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_sw=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_sr=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_raddr=ₑ  paddress′;ₛ
            CSL_MSMC_setSESMPAXL(coreNum′,index′, ses_mpaxl′);ₛ 

            index′ =ₑ ′MPAXSHIPARTIONCUR ;ₛ 
            mpaxh′→mpaxh_segSize  =ₑ ksDomains′[ksCurDomain′]..dom_t_size ;ₛ 
            mpaxh′→mpaxh_bAddr  =ₑ  (ksDomains′[ksCurDomain′]..dom_t_vAddress) ≫ ′12 ;ₛ  
            CSL_XMC_setXMPAXH(index′ ,   mpaxh′);ₛ 

            sms_mpaxh′→smsmpaxh_segSz  =ₑ  ksDomains′[ksCurDomain′]..dom_t_size ;ₛ 
            sms_mpaxh′→smsmpaxh_bAddr  =ₑ (ksDomains′[ksCurDomain′]..dom_t_vAddress) ≫ ′12 ;ₛ  
            CSL_MSMC_setSMSMPAXH(coreNum′ ,index′,  sms_mpaxh′);ₛ 

            ses_mpaxh′→sesmpaxh_segSz  =ₑ ksDomains′[ksCurDomain′]..dom_t_size ;ₛ 
            ses_mpaxh′→sesmpaxh_bAddr  =ₑ (ksDomains′[ksCurDomain′]..dom_t_vAddress) ≫ ′12 ;ₛ   
            CSL_MSMC_setSESMPAXH(coreNum′ , index′ ,   ses_mpaxh′);ₛ 
 

            mpaxl′→mpaxl_ux =ₑ ′1;ₛ 
            mpaxl′→mpaxl_uw =ₑ ′1;ₛ 
            mpaxl′→mpaxl_ur =ₑ ′1;ₛ 
            mpaxl′→mpaxl_sx =ₑ ′1;ₛ 
            mpaxl′→mpaxl_sw =ₑ ′1;ₛ 
            mpaxl′→mpaxl_sr =ₑ ′1;ₛ 
            mpaxl′→mpaxl_rAddr =ₑ ksDomains′[ksCurDomain′]..dom_t_pAddress ≫ ′12 ;ₛ 
            CSL_XMC_setXMPAXL(index′ ,   mpaxl′);ₛ 

            sms_mpaxl′→smsmpaxl_ux =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_uw =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_ur =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_sx =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_sw =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_sr =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_raddr =ₑ  ksDomains′[ksCurDomain′]..dom_t_pAddress ≫ ′12  ;ₛ 
            CSL_MSMC_setSMSMPAXL(coreNum′,index′,  sms_mpaxl′);ₛ 

            ses_mpaxl′→sesmpaxl_ux=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_uw=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_ur=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_sx=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_sw=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_sr=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_raddr=ₑ  ksDomains′[ksCurDomain′]..dom_t_pAddress ≫ ′12  ;ₛ 
            CSL_MSMC_setSESMPAXL(coreNum′,index′, ses_mpaxl′)
            };ₛ 

            index′ =ₑ ′MPAXSHAREDAREA ;ₛ 
            vaddress′ =ₑ ′0x0C000000 ;ₛ 
            paddress′ =ₑ vaddress′ ;ₛ 
            segSize′ =ₑ ′0x13 ;ₛ 

            mpaxh′→mpaxh_segSize  =ₑ segSize′;ₛ 
            mpaxh′→mpaxh_bAddr  =ₑ   vaddress′ ≫ ′12 ;ₛ  
            CSL_XMC_setXMPAXH(index′ ,   mpaxh′);ₛ 

            sms_mpaxh′→smsmpaxh_segSz  =ₑ  segSize′;ₛ  
            sms_mpaxh′→smsmpaxh_bAddr  =ₑ  vaddress′ ≫ ′12 ;ₛ  
            CSL_MSMC_setSMSMPAXH(coreNum′ ,index′,   sms_mpaxh′);ₛ  

            ses_mpaxh′→sesmpaxh_segSz  =ₑ  segSize′;ₛ  
            ses_mpaxh′→sesmpaxh_bAddr  =ₑ  vaddress′ ≫ ′12 ;ₛ   
            CSL_MSMC_setSESMPAXH(coreNum′ , index′ ,   ses_mpaxh′);ₛ   
 
            mpaxl′→mpaxl_ux =ₑ ′1;ₛ 
            mpaxl′→mpaxl_uw =ₑ ′0;ₛ 
            mpaxl′→mpaxl_ur =ₑ ′1;ₛ 
            mpaxl′→mpaxl_sx =ₑ ′1;ₛ 
            mpaxl′→mpaxl_sw =ₑ ′1;ₛ 
            mpaxl′→mpaxl_sr =ₑ ′1;ₛ 
            mpaxl′→mpaxl_rAddr =ₑ paddress′ ≫ ′12 ;ₛ  
            CSL_XMC_setXMPAXL(index′ ,   mpaxl′);ₛ 

            sms_mpaxl′→smsmpaxl_ux =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_uw =ₑ ′0;ₛ 
            sms_mpaxl′→smsmpaxl_ur =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_sx =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_sw =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_sr =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_raddr =ₑ  paddress′ ≫ ′12 ;ₛ  
            CSL_MSMC_setSMSMPAXL(coreNum′,index′,  sms_mpaxl′);ₛ 

            ses_mpaxl′→sesmpaxl_ux=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_uw=ₑ ′0;ₛ 
            ses_mpaxl′→sesmpaxl_ur=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_sx=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_sw=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_sr=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_raddr=ₑ   paddress′ ≫ ′12 ;ₛ  
            CSL_MSMC_setSESMPAXL(coreNum′,index′,  ses_mpaxl′);ₛ 

            index′ =ₑ ′MPAXALLAREA ;ₛ 
            vaddress′ =ₑ ′0x0C000000 ;ₛ 
            paddress′ =ₑ vaddress′ ;ₛ 
            segSize′ =ₑ ′0x15 ;ₛ 

            mpaxh′→mpaxh_segSize  =ₑ segSize′;ₛ 
            mpaxh′→mpaxh_bAddr  =ₑ   vaddress′ ≫ ′12 ;ₛ  
            CSL_XMC_setXMPAXH(index′ ,   mpaxh′);ₛ 

            sms_mpaxh′→smsmpaxh_segSz  =ₑ  segSize′;ₛ  
            sms_mpaxh′→smsmpaxh_bAddr  =ₑ  vaddress′ ≫ ′12 ;ₛ  
            CSL_MSMC_setSMSMPAXH(coreNum′ ,index′,  sms_mpaxh′);ₛ 

            ses_mpaxh′→sesmpaxh_segSz  =ₑ  segSize′;ₛ  
            ses_mpaxh′→sesmpaxh_bAddr  =ₑ  vaddress′ ≫ ′12 ;ₛ   
            CSL_MSMC_setSESMPAXH(coreNum′ , index′ ,  ses_mpaxh′);ₛ
 

            mpaxl′→mpaxl_ux =ₑ ′0;ₛ 
            mpaxl′→mpaxl_uw =ₑ ′0;ₛ 
            mpaxl′→mpaxl_ur =ₑ ′0;ₛ 
            mpaxl′→mpaxl_sx =ₑ ′1;ₛ 
            mpaxl′→mpaxl_sw =ₑ ′1;ₛ 
            mpaxl′→mpaxl_sr =ₑ ′1;ₛ 
            mpaxl′→mpaxl_rAddr =ₑ paddress′ ≫ ′12 ;ₛ  
            CSL_XMC_setXMPAXL(index′ ,   mpaxl′);ₛ 

            sms_mpaxl′→smsmpaxl_ux =ₑ ′0;ₛ 
            sms_mpaxl′→smsmpaxl_uw =ₑ ′0;ₛ 
            sms_mpaxl′→smsmpaxl_ur =ₑ ′0;ₛ 
            sms_mpaxl′→smsmpaxl_sx =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_sw =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_sr =ₑ ′1;ₛ 
            sms_mpaxl′→smsmpaxl_raddr =ₑ  paddress′ ≫ ′12 ;ₛ  
            CSL_MSMC_setSMSMPAXL(coreNum′,index′,  sms_mpaxl′);ₛ  

            ses_mpaxl′→sesmpaxl_ux=ₑ ′0;ₛ 
            ses_mpaxl′→sesmpaxl_uw=ₑ ′0;ₛ 
            ses_mpaxl′→sesmpaxl_ur=ₑ ′0;ₛ 
            ses_mpaxl′→sesmpaxl_sx=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_sw=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_sr=ₑ ′1;ₛ 
            ses_mpaxl′→sesmpaxl_raddr=ₑ   paddress′ ≫ ′12 ;ₛ 
            CSL_MSMC_setSESMPAXL(coreNum′,index′, ses_mpaxl′);ₛ  

          	CSL_XMC_clearFault;ₛ
	          CSL_CGEM_clearMDMAError;ₛ
           RETURN
}· .


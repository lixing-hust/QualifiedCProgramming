Require Import os_ucos_h.
Require Import include_frm.
Require Import os_code_defs.
Require Import ios_cap_defs.
Notation "L '|=ₑ' R" := (sassign L (ebinop obitor L R) ) (at level 70, right associativity) : code_scope.
Notation "A '≤' B" := (ebinop oor (ebinop olt A B) (ebinop oeq A B) ) (at level 57, left associativity)  : code_scope.
Definition EINVAL := 30%Z.
(********************************************辅助函数***************************)
(*Get_Obj_Slot*)

Definition Get_Obj_Slot_impl :=
    Int32u ·Get_Obj_Slot·(⌞prio@Int8u; func_object @ (Void ∗)⌟)··{
    ⌞i@Int32u;
	endPtr@Int32u;
    pCSpace@(CSPACE ∗)
	⌟;
    If(prio′ ≥ ′OS_LOWEST_PRIO){
        RETURN 〈Int32u〉′OS_PRIO_INVALID
    };ₛ
    ENTER_CRITICAL;ₛ
    endPtr′ =ₑ OSCSpaceObjectPointer′[prio′];ₛ
	pCSpace′ =ₑ OSCSpacePrioTbl′[prio′];ₛ
    EXIT_CRITICAL;ₛ
    If(pCSpace′==ₑ〈CSPACE ∗〉 NULL){
        RETURN 〈Int32u〉′SLOT_NULL_CAP
    };ₛ
    i′ =ₑ′OBJ_POSITION;ₛ
    (*这里把for改成while*)
    WHILE(i′ <ₑ endPtr′){
        If(pCSpace′→cnode..slots[i′]..capability..cap_content..object..object_t ==ₑ func_object′){
            RETURN i′
        };ₛ
        ++i′
    };ₛ
    RETURN 〈Int32u〉′SLOT_NULL_CAP
}·.

(* Version of Get_Obj_Slot used within critical regions *)
Definition Get_Obj_Slot_without_critical_impl :=
    Int32u ·Get_Obj_Slot_without_critical·(⌞prio@Int8u; func_object @ (Void ∗)⌟)··{
    ⌞i@Int32u;
	endPtr@Int32u;
    pCSpace@(CSPACE ∗)
	⌟;
    If(prio′ ≥ ′OS_LOWEST_PRIO){
        RETURN 〈Int32u〉′OS_PRIO_INVALID
    };ₛ
    (* If(prio′==ₑ′OS_PRIO_SELF){
        OSPrioCur′ =ₑ OSTCBCur′→OSTCBPrio;ₛ
        prio′ =ₑ OSPrioCur′
    };ₛ *)
    endPtr′ =ₑ OSCSpaceObjectPointer′[prio′];ₛ
	pCSpace′ =ₑ OSCSpacePrioTbl′[prio′];ₛ
    If(pCSpace′==ₑ〈CSPACE ∗〉 NULL){
        RETURN 〈Int32u〉′SLOT_NULL_CAP
    };ₛ
    i′ =ₑ′OBJ_POSITION;ₛ
    WHILE(i′ <ₑ endPtr′){
        If(pCSpace′→cnode..slots[i′]..capability..cap_content..object..object_t ==ₑ func_object′){
            RETURN i′
        };ₛ
        ++i′
    };ₛ
    RETURN 〈Int32u〉′SLOT_NULL_CAP
}·.

(*Check_Cap_Type*)
Definition Check_Cap_Type_impl :=
    Int32s ·Check_Cap_Type·(⌞func_capability@Int32u; func_capType@Int8u;prio@Int8u⌟)··{
    ⌞ret@Int32s⌟;
    If(func_capType′ ==ₑ ′CAP_FUNCTION_TYPE){
        IF(func_capability′ ≤ ′CAP_CHANNEL_CLASS){
            RETURN func_capability′
        }ELSE{
            RETURN 〈Int32s〉′SLOT_NUM
        }
    };ₛ
    (*int ret应该是32位有符号整数*)
    If((func_capType′ ==ₑ ′CAP_SEM_TYPE ||ₑ func_capType′ ==ₑ ′CAP_MUTEX_TYPE ||ₑ  func_capType′ ==ₑ ′CAP_Q_TYPE)
    &&ₑ func_capability′ <ₑ ′OS_USER_MAX_EVENTS ÷ ′3){
       (*SWITCH改写成多个if并列*)
       If(func_capType′ ==ₑ ′CAP_SEM_TYPE){
            If(Sem_info′[func_capability′]..pevent ==ₑ NULL){
                RETURN 〈Int32s〉′SLOT_NUM
            };ₛ
            ret′ =ᶠ Get_Obj_Slot(·prio′, 〈Void ∗〉Sem_info′[func_capability′]..pevent·);ₛ
            (*三目运算符改成if else*)
            IF(ret′==ₑ′SLOT_NULL_CAP){
                RETURN 〈Int32s〉′SLOT_NUM
            }ELSE{
                RETURN 〈Int32s〉ret′
            }
       };ₛ
       If(func_capType′ ==ₑ ′CAP_MUTEX_TYPE){
            If(Pthread_Mutex′[func_capability′]..pevent==ₑNULL){
                RETURN 〈Int32u〉′SLOT_NUM
            };ₛ
            ret′ =ᶠ Get_Obj_Slot(·prio′, 〈Void ∗〉Pthread_Mutex′[func_capability′]..pevent·);ₛ
            IF(ret′==ₑ′SLOT_NULL_CAP){
                RETURN 〈Int32s〉′SLOT_NUM
            }ELSE{
                RETURN 〈Int32s〉ret′
            }
       };ₛ
       If(func_capType′ ==ₑ ′CAP_Q_TYPE){
            If(Mq_Attr′[func_capability′]..pevent==ₑNULL){
                RETURN 〈Int32u〉′SLOT_NUM
            };ₛ
            ret′ =ᶠ Get_Obj_Slot(·prio′,〈Void ∗〉Mq_Attr′[func_capability′]..pevent·);ₛ
            IF(ret′==ₑ′SLOT_NULL_CAP){
                RETURN 〈Int32s〉′SLOT_NUM
            }ELSE{
                RETURN 〈Int32s〉ret′
            }
       };ₛ
       RETURN 〈Int32s〉′EINVAL
    };ₛ
    If(func_capType′==ₑ′CAP_TASK_TYPE &&ₑ func_capability′ <ₑ ′OS_STAT_PRIO
    &&ₑ func_capability′ >ₑ ′0){
        If(OSTCBPrioTbl′[func_capability′]==ₑ〈OS_TCB ∗〉NULL){
            RETURN 〈Int32s〉′SLOT_NUM
        };ₛ
        ret′ =ᶠ Get_Obj_Slot(·prio′, 〈Void ∗〉OSTCBPrioTbl′[func_capability′]·);ₛ
        IF(ret′==ₑ′SLOT_NULL_CAP){
            RETURN 〈Int32s〉′SLOT_NUM
        }ELSE{
            RETURN 〈Int32s〉ret′
        }
    };ₛ
    RETURN 〈Int32s〉′SLOT_NUM
}·.


(*CNode_delete_recursive *)
Definition CNode_delete_recursive_impl :=
    Void ·CNode_delete_recursive·(⌞dest_space@CSPACE ∗; func_capType@Int8u; func_capability@Int32u⌟)··{
    ⌞i@Int32u;
	cap1@ Cap ∗;
    x@Int32u⌟;
    i′ =ₑ ′0;ₛ 
    ENTER_CRITICAL;ₛ
    x′ =ᶠ Check_Cap_Type(·func_capability′, func_capType′, 〈Int8u〉dest_space′→taskPrio·);ₛ 
    (*两个if的条件互斥，所以可以把if else if写成两个单独的if*)
    EXIT_CRITICAL;ₛ
    If(x′!=ₑ ′SLOT_NUM){
        cap1′ =ₑ &ₐ(dest_space′→cnode..slots[x′]..capability);ₛ
        IF(cap1′→cap_type==ₑ′CAP_CATEGORY_TYPE){
            cap1′→cap_type =ₑ ′0;ₛ
            cap1′→cap_content..category..category_content =ₑ′0;ₛ
            cap1′→cap_content..category..category_right =ₑ ′0
        }ELSE{
            If(cap1′→cap_type==ₑ′CAP_OBJECT_TYPE){
                cap1′→cap_type =ₑ ′0;ₛ
                cap1′→cap_content..object..object_right =ₑ′0;ₛ
                cap1′→cap_content..object..object_t =ₑ〈Void ∗〉NULL
            }
        };ₛ
        dest_space′→cnode..slots[x′]..slot_type =ₑ ′SLOT_NULL_CAP
    };ₛ
    WHILE(i′ <ₑ dest_space′→child_num){
        scall CNode_delete_recursive(〈CSPACE ∗〉dest_space′→cspace_children[i′]::func_capType′::func_capability′::nil);ₛ
        ++i′
    };ₛ
    RETURN 
}·.



(******************************************内核函数**********************************)
(*ucos_Grant_Cap*)
Definition ucos_Grant_Cap_impl :=
    Int8u ·ucos_Grant_Cap·(⌞destTask_Prio@Int8u; cap_Class@Int32u; cap_Right@Int32u⌟)··{
    ⌞⌟;
    If(′CAP_NULL_CLASS >ₑ cap_Class′ ||ₑ cap_Class′ >ₑ ′CAP_CHANNEL_CLASS){
        RETURN ′CNODE_GRANT_FAILURE
    };ₛ
    If(destTask_Prio′ ≥ ′64){
        RETURN ′CNODE_GRANT_FAILURE
    };ₛ
    If(OSCSpacePrioTbl′[destTask_Prio′] ==ₑ 〈CSPACE ∗〉NULL){
        RETURN ′CNODE_GRANT_FAILURE
    };ₛ
    OSCSpacePrioTbl′[destTask_Prio′]→cnode..slots[cap_Class′]..capability..cap_type =ₑ ′CAP_CATEGORY_TYPE;ₛ
    OSCSpacePrioTbl′[destTask_Prio′]→cnode..slots[cap_Class′]..capability..cap_content..category..category_content =ₑcap_Class′;ₛ
    OSCSpacePrioTbl′[destTask_Prio′]→cnode..slots[cap_Class′]..capability..cap_content..category..category_right &= ′4095;ₛ
    OSCSpacePrioTbl′[destTask_Prio′]→cnode..slots[cap_Class′]..capability..cap_content..category..category_right |=ₑ cap_Right′;ₛ
    RETURN 〈Int8u〉′0
}·.




(*ucos_CNode_Mint*)

Definition ucos_CNode_Mint_impl :=
    Int8u ·ucos_CNode_Mint·(⌞destTask_Prio@Int8u; srcTask_Prio@Int8u; func_capability@Int32u; rights@Int32u⌟)··{
    ⌞pCSpace1@CSPACE ∗;
	pCSpace2@CSPACE ∗;
	cap1@Cap ∗;
	cap2@Cap ∗⌟;
    If(′CAP_NULL_CLASS >ₑ func_capability′ ||ₑ func_capability′ >ₑ ′CAP_CHANNEL_CLASS){
        RETURN ′CNODE_MINT_FAILURE
    };ₛ
    If(destTask_Prio′ ≥ ′64||ₑsrcTask_Prio′ ≥ ′64){
        RETURN ′CNODE_MINT_FAILURE
    };ₛ
    pCSpace1′ =ₑ OSCSpacePrioTbl′[destTask_Prio′];ₛ
    pCSpace2′ =ₑ OSCSpacePrioTbl′[srcTask_Prio′];ₛ
    If(pCSpace1′ ==ₑ 〈CSPACE ∗〉NULL ||ₑ pCSpace2′ ==ₑ 〈CSPACE ∗〉NULL){
        RETURN ′CNODE_MINT_FAILURE
    };ₛ

    cap1′ =ₑ &ₐ(pCSpace1′→cnode..slots[func_capability′]..capability);ₛ
    cap2′ =ₑ &ₐ(pCSpace2′→cnode..slots[func_capability′]..capability);ₛ
    IF(cap2′→cap_type==ₑ′CAP_CATEGORY_TYPE&&ₑ((∼cap2′→cap_content..category..category_right)&ₑrights′)==ₑ′0&&ₑcap2′→cap_content..category..category_right !=ₑ rights′){
        cap1′→cap_type =ₑ ′CAP_CATEGORY_TYPE;ₛ
        cap1′→cap_content..category..category_content =ₑ cap2′→cap_content..category..category_content;ₛ
        cap1′→cap_content..category..category_right =ₑ rights′

    }ELSE{
        RETURN 〈Int8u〉′CNODE_MINT_FAILURE
    };ₛ
    
    RETURN 〈Int8u〉′CNODE_NONE_FAULT
    
}·.


(*~ ! 0 1*)
(*ucos_CNode_Copy*)
Definition ucos_CNode_Copy_impl :=
    Int8u ·ucos_CNode_Copy·(⌞destTask_Prio@Int8u; srcTask_Prio@Int8u; func_capability@Int32u⌟)··{
    ⌞
    idx@Int32u;
    pCSpace1@CSPACE ∗;
	pCSpace2@CSPACE ∗;
	cap1@Cap ∗;
	cap2@Cap ∗⌟;
    cap1′=ₑ〈Cap ∗〉NULL;ₛ
    cap2′=ₑ〈Cap ∗〉NULL;ₛ
    If(func_capability′ ≥ ′SLOT_NUM){
        RETURN ′CNODE_COPY_FAILURE
    };ₛ
    If(destTask_Prio′ ≥ ′64||ₑsrcTask_Prio′ ≥ ′64){
        RETURN ′CNODE_COPY_FAILURE
    };ₛ
    pCSpace1′ =ₑ OSCSpacePrioTbl′[destTask_Prio′];ₛ
    pCSpace2′ =ₑ OSCSpacePrioTbl′[srcTask_Prio′];ₛ
    If(pCSpace1′ ==ₑ 〈CSPACE ∗〉NULL ||ₑ pCSpace2′ ==ₑ 〈CSPACE ∗〉NULL){
        RETURN ′CNODE_COPY_FAILURE
    };ₛ
    cap1′ =ₑ &ₐ(pCSpace1′→cnode..slots[func_capability′]..capability);ₛ
    cap2′ =ₑ &ₐ(pCSpace2′→cnode..slots[func_capability′]..capability);ₛ
(*这里稍许做了些改动，框架没有实现if elseif else的操作,可以等价为两个if else{if else{}}*)
    IF(cap2′→cap_type==ₑ′CAP_CATEGORY_TYPE){
        cap1′→cap_type =ₑ ′CAP_CATEGORY_TYPE;ₛ
        cap1′→cap_content..category..category_content =ₑ cap2′→cap_content..category..category_content;ₛ
        cap1′→cap_content..category..category_right =ₑ cap2′→cap_content..category..category_right
    }ELSE{
        IF(cap2′→cap_type==ₑ′CAP_OBJECT_TYPE){
            idx′ =ᶠ Get_Obj_Slot(·destTask_Prio′ ,cap2′→cap_content..object..object_t·);ₛ
            If(idx′==ₑ′SLOT_NULL_CAP){
                idx′ =ₑ OSCSpaceObjectPointer′[destTask_Prio′];ₛ
                If(idx′≥′SLOT_NUM){
                    RETURN ′SLOT_RANGE_OVERFLOW
                };ₛ
			    ++OSCSpaceObjectPointer′[destTask_Prio′]
            };ₛ
            cap1′ =ₑ &ₐ(pCSpace1′→cnode..slots[idx′]..capability);ₛ
            cap1′→cap_type =ₑ ′CAP_OBJECT_TYPE;ₛ
            cap1′→cap_content..object..object_right =ₑ cap2′→cap_content..object..object_right;ₛ
            cap1′→cap_content..object..object_t =ₑ cap2′→cap_content..object..object_t;ₛ
             
            RETURN 〈Int8u〉′CNODE_NONE_FAULT  (*在这里加上一个return,没有影响程序的正确性，证明起来的时候减少了中间生成变量的影响
            *)
        }ELSE{
            RETURN ′CNODE_COPY_FAILURE
        }
    };ₛ
    RETURN 〈Int8u〉′CNODE_NONE_FAULT
}·.


(*ucos_CNode_Move*)
Definition ucos_CNode_Move_impl :=
    Int8u ·ucos_CNode_Move·(⌞destTask_Prio@Int8u; srcTask_Prio@Int8u; func_capability@Int32u⌟)··{
    ⌞
    idx@Int32u;
    pCSpace1@CSPACE ∗;
	pCSpace2@CSPACE ∗;
	cap1@Cap ∗;
	cap2@Cap ∗⌟;
    If(func_capability′ ≥ ′SLOT_NUM){
        RETURN ′CNODE_MOVE_FAILURE
    };ₛ
    If(destTask_Prio′ ≥ ′64||ₑsrcTask_Prio′ ≥ ′64){
        RETURN ′CNODE_MOVE_FAILURE
    };ₛ
    pCSpace1′ =ₑ OSCSpacePrioTbl′[destTask_Prio′];ₛ
    pCSpace2′ =ₑ OSCSpacePrioTbl′[srcTask_Prio′];ₛ
    If(pCSpace1′ ==ₑ 〈CSPACE ∗〉NULL ||ₑ pCSpace2′ ==ₑ 〈CSPACE ∗〉NULL){
        RETURN ′CNODE_MOVE_FAILURE
    };ₛ
    cap1′ =ₑ &ₐ(pCSpace1′→cnode..slots[func_capability′]..capability);ₛ
    cap2′ =ₑ &ₐ(pCSpace2′→cnode..slots[func_capability′]..capability);ₛ
(*这里稍许做了些改动，框架没有实现if elseif else的操作,可以等价为两个if else{if else{}}*)
    IF(cap2′→cap_type==ₑ′CAP_CATEGORY_TYPE){
        cap1′→cap_type =ₑ ′CAP_CATEGORY_TYPE;ₛ
        cap1′→cap_content..category..category_content =ₑ cap2′→cap_content..category..category_content;ₛ
        cap1′→cap_content..category..category_right =ₑ cap2′→cap_content..category..category_right;ₛ

        cap2′→cap_type =ₑ ′0;ₛ
        cap2′→cap_content..category..category_content =ₑ′0;ₛ
        cap2′→cap_content..category..category_right =ₑ ′0
    }ELSE{
        IF(cap2′→cap_type==ₑ′CAP_OBJECT_TYPE){
            idx′ =ᶠ Get_Obj_Slot(·destTask_Prio′ ,cap2′→cap_content..object..object_t·);ₛ
            If(idx′==ₑ′SLOT_NULL_CAP){
                idx′ =ₑ OSCSpaceObjectPointer′[destTask_Prio′];ₛ
                If(idx′≥′SLOT_NUM){
                    RETURN ′SLOT_RANGE_OVERFLOW
                };ₛ
                ++OSCSpaceObjectPointer′[destTask_Prio′]
            };ₛ
            cap1′ =ₑ &ₐ(pCSpace1′→cnode..slots[idx′]..capability);ₛ
            cap1′→cap_type =ₑ ′CAP_OBJECT_TYPE;ₛ
            cap1′→cap_content..object..object_right =ₑ cap2′→cap_content..object..object_right;ₛ
            cap1′→cap_content..object..object_t =ₑ cap2′→cap_content..object..object_t;ₛ
            
            cap2′→cap_type =ₑ ′0;ₛ
            cap2′→cap_content..object..object_right =ₑ ′0;ₛ
            cap2′→cap_content..object..object_t =ₑ〈Void ∗〉NULL;ₛ
        
            pCSpace2′→cnode..slots[func_capability′]..slot_type =ₑ ′SLOT_NULL_CAP;ₛ
            RETURN 〈Int8u〉′CNODE_NONE_FAULT
        }ELSE{
            RETURN 〈Int8u〉′CNODE_MOVE_FAILURE
        }
    };ₛ
    pCSpace2′→cnode..slots[func_capability′]..slot_type =ₑ ′SLOT_NULL_CAP;ₛ
    RETURN 〈Int8u〉′CNODE_NONE_FAULT

}·.


(*ucos_CNode_Mutate*)
Definition ucos_CNode_Mutate_impl :=
    Int8u ·ucos_CNode_Mutate·(⌞destTask_Prio@Int8u; srcTask_Prio@Int8u; func_capability@Int32u; rights@Int32u⌟)··{
    ⌞
    pCSpace1@CSPACE ∗;
	pCSpace2@CSPACE ∗;
	cap1@Cap ∗;
	cap2@Cap ∗⌟;
    If(′CAP_NULL_CLASS >ₑ func_capability′ ||ₑ func_capability′ >ₑ ′CAP_CHANNEL_CLASS){
        RETURN ′CNODE_MUTATE_FAILURE
    };ₛ
    If(destTask_Prio′ ≥ ′64||ₑsrcTask_Prio′ ≥ ′64){
        RETURN ′CNODE_MUTATE_FAILURE
    };ₛ
    pCSpace1′ =ₑ OSCSpacePrioTbl′[destTask_Prio′];ₛ
    pCSpace2′ =ₑ OSCSpacePrioTbl′[srcTask_Prio′];ₛ
    If(pCSpace1′ ==ₑ 〈CSPACE ∗〉NULL ||ₑ pCSpace2′ ==ₑ 〈CSPACE ∗〉NULL){
        RETURN ′CNODE_MUTATE_FAILURE
    };ₛ

    cap1′ =ₑ &ₐ(pCSpace1′→cnode..slots[func_capability′]..capability);ₛ
    cap2′ =ₑ &ₐ(pCSpace2′→cnode..slots[func_capability′]..capability);ₛ
    IF(cap2′→cap_type==ₑ′CAP_CATEGORY_TYPE&&ₑ((∼cap2′→cap_content..category..category_right)&ₑrights′)==ₑ′0&&ₑcap2′→cap_content..category..category_right !=ₑ rights′){
        cap1′→cap_type =ₑ ′CAP_CATEGORY_TYPE;ₛ
        cap1′→cap_content..category..category_content =ₑ cap2′→cap_content..category..category_content;ₛ
        cap1′→cap_content..category..category_right =ₑ rights′;ₛ
        cap2′→cap_content..category..category_right &= (∼rights′)
    }ELSE{
        RETURN 〈Int8u〉′CNODE_MUTATE_FAILURE
    };ₛ
    pCSpace2′→cnode..slots[func_capability′]..slot_type =ₑ ′SLOT_NULL_CAP;ₛ
    RETURN 〈Int8u〉′CNODE_NONE_FAULT
}·.


(*ucos_CNode_Delete*)
Definition ucos_CNode_Delete_impl :=
    Int8u ·ucos_CNode_Delete·(⌞destTask_Prio@Int8u;  func_capability@Int32u⌟)··{
    ⌞
    pCSpace1@CSPACE ∗;
	cap1@Cap ∗⌟;
    (*为了防止跟struct名重名，这里把cap改名为cap1*)
    If(func_capability′ ≥ ′SLOT_NUM){
        RETURN ′CNODE_DELETE_FAILURE
    };ₛ
    If(destTask_Prio′ ≥ ′64){
        RETURN ′CNODE_DELETE_FAILURE
    };ₛ
    pCSpace1′ =ₑ OSCSpacePrioTbl′[destTask_Prio′];ₛ
    If(pCSpace1′ ==ₑ 〈CSPACE ∗〉NULL ){
        RETURN ′CNODE_DELETE_FAILURE
    };ₛ

    cap1′ =ₑ &ₐ(pCSpace1′→cnode..slots[func_capability′]..capability);ₛ
(*这里稍许做了些改动，框架没有实现if elseif else的操作,可以等价为两个if else{if else{}}*)
    IF(cap1′→cap_type==ₑ′CAP_CATEGORY_TYPE){
        cap1′→cap_type =ₑ ′0;ₛ
        cap1′→cap_content..category..category_content =ₑ′0;ₛ
        cap1′→cap_content..category..category_right =ₑ ′0
    }ELSE{
        IF(cap1′→cap_type==ₑ′CAP_OBJECT_TYPE){
            cap1′→cap_type =ₑ ′0;ₛ
            cap1′→cap_content..object..object_right =ₑ′0;ₛ
            cap1′→cap_content..object..object_t =ₑ〈Void ∗〉NULL
        }ELSE{
            RETURN 〈Int8u〉′CNODE_DELETE_FAILURE
        }
    };ₛ
    pCSpace1′→cnode..slots[func_capability′]..slot_type =ₑ ′SLOT_NULL_CAP;ₛ
    RETURN 〈Int8u〉′CNODE_NONE_FAULT

}·.

(*ucos_CNode_Revoke*)
Definition ucos_CNode_Revoke_impl :=
    Int8u ·ucos_CNode_Revoke·(⌞destTask_Prio@Int8u; func_capType@Int8u;func_capability@Int32u⌟)··{
    ⌞pCSpace@CSPACE ∗⌟;
    If(destTask_Prio′ ≥ ′64){
        RETURN ′OS_PRIO_INVALID
    };ₛ
    pCSpace′ =ₑ OSCSpacePrioTbl′[destTask_Prio′];ₛ

    IF(pCSpace′ !=ₑ NULL){
    scall CNode_delete_recursive(pCSpace′::func_capType′::func_capability′::nil)
    }ELSE{
        RETURN 〈Int8u〉′OS_PRIO_INVALID
    };ₛ
    RETURN 〈Int8u〉′CNODE_NONE_FAULT

}·.



(********************************************用户函数********************************)
Definition grant_cspace_cap_impl :=
    Int8u ·grant_cspace_cap·(⌞destTask_Prio@Int8u; cap_Class@Int32u; cap_Right@Int32u⌟)··{
    ⌞i @ Int8u;
    pCSpace@CSPACE ∗⌟;   
    If(destTask_Prio′ ≥ ′OS_LOWEST_PRIO){
        RETURN 〈Int8u〉′OS_PRIO_INVALID
    };ₛ
    ENTER_CRITICAL;ₛ
    OSPrioCur′ =ₑ OSTCBCur′→OSTCBPrio;ₛ
    pCSpace′=ₑOSCSpacePrioTbl′[OSPrioCur′];ₛ
    If(pCSpace′ ==ₑ〈CSPACE∗〉 NULL){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′CNODE_GRANT_FAILURE
    };ₛ
    IF(OSRunning′ ==ₑ CFalse ||ₑ (pCSpace′→cnode..slots[′SLOT_CNODE_CAP]
    ..capability..cap_content..category..category_right &ₑ ′CNODE_GRANT_CAP) !=ₑ ′0 &&ₑ
    CapParent′[destTask_Prio′] ==ₑ OSPrioCur′){
        i′ =ᶠ ucos_Grant_Cap(·destTask_Prio′,cap_Class′,cap_Right′·);ₛ
        IF(i′==ₑ′CNODE_NONE_FAULT){
            EXIT_CRITICAL;ₛ
            RETURN 〈Int8u〉′CSPACE_NONE_FAULT
        }ELSE{
            EXIT_CRITICAL;ₛ
            RETURN 〈Int8u〉′CNODE_GRANT_FAILURE
        }
    }ELSE{
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′USER_CAPABILITY_NONE
    }
    
}·.

Definition user_cnode_mint_impl := 
    Int8u ·user_cnode_mint·(⌞destTask_Prio@Int8u; srcTask_Prio@Int8u; func_capability@Int32u; rights@Int32u⌟)··{
    ⌞pCSpace@CSPACE ∗;
    i @ Int8u;
    y @ Int8u⌟;
    If((srcTask_Prio′≥′OS_LOWEST_PRIO ) ||ₑ
    (destTask_Prio′ ≥ ′OS_LOWEST_PRIO )){
        RETURN 〈Int8u〉′OS_PRIO_INVALID
    };ₛ
    ENTER_CRITICAL;ₛ
    y′ =ₑ OSTCBCur′→OSTCBPrio;ₛ
    pCSpace′=ₑOSCSpacePrioTbl′[y′];ₛ
    If(pCSpace′ ==ₑ〈CSPACE∗〉 NULL){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′CNODE_MINT_FAILURE
    };ₛ
    (*没有定义!这个操作，所以!(a&&b) 等价于 !a || !b*)
    IF((pCSpace′→cnode..slots[′SLOT_CNODE_CAP]..capability..cap_content..category..category_right &ₑ ′CNODE_MINT_CAP) ==ₑ ′0
    ||ₑ CapParent′[destTask_Prio′] !=ₑ srcTask_Prio′){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′USER_CAPABILITY_NONE
    }ELSE{
        (*这里使用临时变量记录函数返回值*)
        i′ =ᶠ ucos_CNode_Mint(·destTask_Prio′, srcTask_Prio′, func_capability′, rights′·);ₛ
        IF(i′==ₑ′CNODE_NONE_FAULT){
            EXIT_CRITICAL;ₛ
            RETURN 〈Int8u〉′CNODE_MINT_SUCCESS
        }ELSE{
            EXIT_CRITICAL;ₛ
            RETURN 〈Int8u〉′CNODE_MINT_FAILURE
        }
    }
}·.

Definition user_cnode_copy_impl :=
    Int8u ·user_cnode_copy·(⌞destTask_Prio@Int8u; srcTask_Prio@Int8u;func_capType@Int8u; func_capability@Int32u⌟)··{
    ⌞
    pCSpace@CSPACE ∗;
	  index@Int32u;
    i @ Int8u;
    y @ Int8u⌟;
    If((srcTask_Prio′≥′OS_LOWEST_PRIO ) ||ₑ
    (destTask_Prio′ ≥ ′OS_LOWEST_PRIO)){
        RETURN 〈Int8u〉′OS_PRIO_INVALID
    };ₛ
    ENTER_CRITICAL;ₛ
    If(func_capType′ >ₑ ′CAP_TASK_TYPE){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′EINVAL
    };ₛ    
    index′=ᶠCheck_Cap_Type(·func_capability′, func_capType′, srcTask_Prio′·);ₛ
    If(index′==ₑ′SLOT_NUM){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′EINVAL
    };ₛ
    y′ =ₑ OSTCBCur′→OSTCBPrio;ₛ
    pCSpace′=ₑOSCSpacePrioTbl′[y′];ₛ
    If(pCSpace′ ==ₑ〈CSPACE∗〉 NULL){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′CNODE_COPY_FAILURE
    };ₛ
    (*没有定义!这个操作，所以!(a&&b) 等价于 !a || !b*)
    IF((pCSpace′→cnode..slots[′SLOT_CNODE_CAP]..capability..cap_content..category..category_right &ₑ ′CNODE_COPY_CAP) ==ₑ ′0
    ||ₑ CapParent′[destTask_Prio′] !=ₑ srcTask_Prio′){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′USER_CAPABILITY_NONE
    }ELSE{
         (*这里使用临时变量记录函数返回值*)
        i′ =ᶠ ucos_CNode_Copy(·destTask_Prio′, srcTask_Prio′, index′·);ₛ
        IF(i′==ₑ′CNODE_NONE_FAULT){
            (*If(func_capType′ ==ₑ ′CAP_TASK_TYPE){
                OSTCBPrioTbl′[func_capability′]→TCBCap[destTask_Prio′ − ′OS_N_SYS_TASKS] =ᶠ Get_Obj_Slot(·destTask_Prio′, OSTCBPrioTbl′[func_capability′]·)
            };ₛ
            If(func_capType′ ==ₑ ′CAP_SEM_TYPE){
                Sem_info′[func_capability′]..sem_cap[destTask_Prio′ − ′OS_N_SYS_TASKS] =ᶠ Get_Obj_Slot(·destTask_Prio′, Sem_info′[func_capability′]..pevent·)
            };ₛ
            If(func_capType′ ==ₑ ′CAP_MUTEX_TYPE){
                Pthread_Mutex′[func_capability′]..mutex_cap[destTask_Prio′ − ′OS_N_SYS_TASKS] =ᶠ Get_Obj_Slot(·destTask_Prio′, Pthread_Mutex′[func_capability′]..pevent·)
            };ₛ
            If(func_capType′ ==ₑ ′CAP_Q_TYPE){
                Mq_Attr′[func_capability′]..mq_cap[destTask_Prio′ − ′OS_N_SYS_TASKS] =ᶠ Get_Obj_Slot(·destTask_Prio′, Mq_Attr′[func_capability′]..pevent·)
            };ₛ*)
            EXIT_CRITICAL;ₛ
            RETURN 〈Int8u〉′CNODE_COPY_SUCCESS
        }ELSE{
            EXIT_CRITICAL;ₛ
            RETURN 〈Int8u〉′CNODE_COPY_FAILURE
        }
    }
    
}·.

Definition user_cnode_move_impl :=
    Int8u ·user_cnode_move·(⌞destTask_Prio@Int8u; srcTask_Prio@Int8u;func_capType@Int8u; func_capability@Int32u⌟)··{
    ⌞
    pCSpace@CSPACE ∗;
	index@Int32u;
    i @ Int8u;
    y @ Int8u ⌟;
    If((srcTask_Prio′≥′OS_LOWEST_PRIO) ||ₑ
    (destTask_Prio′ ≥ ′OS_LOWEST_PRIO)){
        RETURN 〈Int8u〉′OS_PRIO_INVALID
    };ₛ
    ENTER_CRITICAL;ₛ
    If(func_capType′ >ₑ ′CAP_TASK_TYPE){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′EINVAL
    };ₛ
    index′=ᶠCheck_Cap_Type(·func_capability′, func_capType′, srcTask_Prio′·);ₛ
    If(index′==ₑ′SLOT_NUM){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′EINVAL
    };ₛ
    y′ =ₑ OSTCBCur′→OSTCBPrio;ₛ
    pCSpace′=ₑOSCSpacePrioTbl′[y′];ₛ
    If(pCSpace′ ==ₑ〈CSPACE∗〉 NULL){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′CNODE_MOVE_FAILURE
    };ₛ
    (*没有定义!这个操作，所以!(a&&b) 等价于 !a || !b*)
    IF((pCSpace′→cnode..slots[′SLOT_CNODE_CAP]..capability..cap_content..category..category_right &ₑ ′CNODE_MOVE_CAP) ==ₑ ′0
    ||ₑ CapParent′[destTask_Prio′] !=ₑ srcTask_Prio′){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′USER_CAPABILITY_NONE
    }ELSE{
        (*这里使用临时变量记录函数返回值*)
        i′ =ᶠ ucos_CNode_Move(·destTask_Prio′, srcTask_Prio′, index′·);ₛ
        IF(i′==ₑ′CNODE_NONE_FAULT){
            (* If(func_capType′ ==ₑ ′CAP_TASK_TYPE){
                OSTCBPrioTbl′[func_capability′]→TCBCap[destTask_Prio′ − ′OS_N_SYS_TASKS] =ᶠ Get_Obj_Slot(·destTask_Prio′, OSTCBPrioTbl′[func_capability′]·)
            };ₛ 
            If(func_capType′ ==ₑ ′CAP_SEM_TYPE){
                Sem_info′[func_capability′]..sem_cap[destTask_Prio′ − ′OS_N_SYS_TASKS] =ᶠ Get_Obj_Slot(·destTask_Prio′, 〈Void ∗〉Sem_info′[func_capability′]..pevent·);ₛ
            };ₛ
             If(func_capType′ ==ₑ ′CAP_MUTEX_TYPE){
                Pthread_Mutex′[func_capability′]..mutex_cap[destTask_Prio′ − ′OS_N_SYS_TASKS] =ᶠ Get_Obj_Slot(·destTask_Prio′, Pthread_Mutex′[func_capability′]..pevent·)
            };ₛ
            If(func_capType′ ==ₑ ′CAP_Q_TYPE){
                Mq_Attr′[func_capability′]..mq_cap[destTask_Prio′ − ′OS_N_SYS_TASKS] =ᶠ Get_Obj_Slot(·destTask_Prio′, Mq_Attr′[func_capability′]..pevent·)
            };ₛ  *)
            EXIT_CRITICAL;ₛ
            RETURN 〈Int8u〉′CNODE_MOVE_SUCCESS
        }ELSE{
            EXIT_CRITICAL;ₛ
            RETURN 〈Int8u〉′CNODE_MOVE_FAILURE
        }
    }
    
}·.

Definition user_cnode_mutate_impl := 
    Int8u ·user_cnode_mutate·(⌞destTask_Prio@Int8u; srcTask_Prio@Int8u; func_capability@Int32u; rights@Int32u⌟)··{
    ⌞pCSpace@CSPACE ∗;
    i @ Int8u;
    y @ Int8u⌟;
    If((srcTask_Prio′≥′OS_LOWEST_PRIO ) ||ₑ(destTask_Prio′ ≥ ′OS_LOWEST_PRIO)){
        RETURN 〈Int8u〉′OS_PRIO_INVALID
    };ₛ
    ENTER_CRITICAL;ₛ    
    y′ =ₑ OSTCBCur′→OSTCBPrio;ₛ
    pCSpace′=ₑOSCSpacePrioTbl′[y′];ₛ
    If(pCSpace′ ==ₑ〈CSPACE∗〉 NULL){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′CNODE_MUTATE_FAILURE
    };ₛ
    (*没有定义!这个操作，所以!(a&&b) 等价于 !a || !b*)
    IF((pCSpace′→cnode..slots[′SLOT_CNODE_CAP]..capability..cap_content..category..category_right &ₑ ′CNODE_MUTATE_CAP) ==ₑ ′0
    ||ₑ (CapParent′[destTask_Prio′] !=ₑ srcTask_Prio′)){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′USER_CAPABILITY_NONE
    }ELSE{
        (*这里使用临时变量记录函数返回值*)
        i′ =ᶠ ucos_CNode_Mutate(·destTask_Prio′, srcTask_Prio′, func_capability′, rights′·);ₛ
        IF(i′==ₑ′CNODE_NONE_FAULT){
            EXIT_CRITICAL;ₛ
            RETURN 〈Int8u〉′CNODE_MUTATE_SUCCESS
        }ELSE{
            EXIT_CRITICAL;ₛ
            RETURN 〈Int8u〉′CNODE_MUTATE_FAILURE
        }
    }
}·.

Definition user_cnode_delete_impl := 
    Int8u ·user_cnode_delete·(⌞destTask_Prio@Int8u; func_capType@Int8u; func_capability@Int32u⌟)··{
    ⌞pCSpace@CSPACE ∗;
    i @ Int8u;
    y @ Int8u⌟;
    If((destTask_Prio′ ≥ ′OS_LOWEST_PRIO)){
        RETURN 〈Int8u〉′OS_PRIO_INVALID
    };ₛ
    ENTER_CRITICAL;ₛ
    If(func_capType′ >ₑ ′CAP_TASK_TYPE){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′EINVAL
    };ₛ
    
    func_capability′=ᶠCheck_Cap_Type(·func_capability′, func_capType′, destTask_Prio′·);ₛ
    If(func_capability′==ₑ′SLOT_NUM){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′EINVAL
    };ₛ
    y′ =ₑ OSTCBCur′→OSTCBPrio;ₛ
    pCSpace′=ₑOSCSpacePrioTbl′[y′];ₛ
    If(pCSpace′ ==ₑ〈CSPACE∗〉 NULL){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′CNODE_DELETE_FAILURE
    };ₛ
    (*没有定义!这个操作，所以!(a&&b) 等价于 !a || !b*)
    IF((pCSpace′→cnode..slots[′SLOT_CNODE_CAP]..capability..cap_content..category..category_right &ₑ ′CNODE_DELETE_CAP) ==ₑ ′0
    ||ₑ (CapParent′[destTask_Prio′] !=ₑ OSTCBCur′→OSTCBPrio &&ₑ destTask_Prio′ !=ₑ OSTCBCur′→OSTCBPrio)){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′USER_CAPABILITY_NONE
    }ELSE{
        (*这里使用临时变量记录函数返回值*)
        i′ =ᶠ ucos_CNode_Delete(·destTask_Prio′, func_capability′·);ₛ
        IF(i′==ₑ′CNODE_NONE_FAULT){
            EXIT_CRITICAL;ₛ
            RETURN 〈Int8u〉′CNODE_DELETE_SUCCESS
        }ELSE{
            EXIT_CRITICAL;ₛ
            RETURN 〈Int8u〉′CNODE_DELETE_FAILURE
        }
    }
}·.

Definition user_cnode_revoke_impl := 
    Int8u ·user_cnode_revoke·(⌞destTask_Prio@Int8u; func_capType@Int8u; func_capability@Int32u⌟)··{
    ⌞pCSpace@CSPACE ∗;
    i @ Int8u;
    y @ Int8u⌟;
    If((destTask_Prio′ ≥ ′OS_LOWEST_PRIO)){
        RETURN 〈Int8u〉′OS_PRIO_INVALID
    };ₛ
    ENTER_CRITICAL;ₛ
    If(func_capType′ >ₑ ′CAP_TASK_TYPE){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′EINVAL
    };ₛ
    func_capability′=ᶠCheck_Cap_Type(·func_capability′, func_capType′, destTask_Prio′·);ₛ
    If(func_capability′==ₑ′SLOT_NUM){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′EINVAL
    };ₛ
    y′ =ₑ OSTCBCur′→OSTCBPrio;ₛ
    pCSpace′=ₑOSCSpacePrioTbl′[y′];ₛ
    If(pCSpace′ ==ₑ〈CSPACE∗〉 NULL){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′CNODE_REVOKE_FAILURE
    };ₛ
    (*没有定义!这个操作，所以!(a&&b) 等价于 !a || !b*)
    IF((pCSpace′→cnode..slots[′SLOT_CNODE_CAP]..capability..cap_content..category..category_right &ₑ ′CNODE_REVOKE_CAP) ==ₑ ′0
    ||ₑ (CapParent′[destTask_Prio′] !=ₑ OSTCBCur′→OSTCBPrio &&ₑ destTask_Prio′ !=ₑ OSTCBCur′→OSTCBPrio)){
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′USER_CAPABILITY_NONE
    }ELSE{
        (*这里使用临时变量记录函数返回值*)
        i′ =ᶠ ucos_CNode_Revoke(·destTask_Prio′, func_capType′, func_capability′·);ₛ
        IF(i′==ₑ′CNODE_NONE_FAULT){
            EXIT_CRITICAL;ₛ
            RETURN 〈Int8u〉′CNODE_REVOKE_SUCCESS
        }ELSE{
            EXIT_CRITICAL;ₛ
            RETURN 〈Int8u〉′CNODE_REVOKE_FAILURE
        }
    }
}·.


Definition cspace_create_empty_impl :=
    Int8u ·cspace_create_empty·(⌞destTask_Prio@Int8u⌟)··{
        ⌞pCSpace@CSPACE ∗⌟;
        ENTER_CRITICAL;ₛ
        If(OSCSpacePrioTbl′[destTask_Prio′] ==ₑ 〈CSPACE ∗〉NULL) {
            pCSpace′ =ₑ OSCSpaceFreeList′;ₛ
            OSCSpaceFreeList′ =ₑ OSCSpaceFreeList′→OSCSpaceNext;ₛ
            OSCSpacePrioTbl′[destTask_Prio′] =ₑ pCSpace′;ₛ
            OSCSpaceObjectPointer′[destTask_Prio′] =ₑ ′OBJ_POSITION;ₛ
            pCSpace′→child_num =ₑ ′0;ₛ
            pCSpace′→cnode..guide_num =ₑ ′8;ₛ
            pCSpace′→cnode..slot_num =ₑ ′8;ₛ
            ucos_CNode_Delete(-destTask_Prio′, ′CAP_TASK_CLASS-);ₛ
            ucos_CNode_Delete(-destTask_Prio′, ′CAP_TIME_CLASS-);ₛ
            ucos_CNode_Delete(-destTask_Prio′, ′CAP_MBOX_CLASS-);ₛ
            ucos_CNode_Delete(-destTask_Prio′, ′CAP_QUEUE_CLASS-);ₛ
            ucos_CNode_Delete(-destTask_Prio′, ′CAP_MUTEX_CLASS-);ₛ
            ucos_CNode_Delete(-destTask_Prio′, ′CAP_SEM_CLASS-);ₛ
            ucos_CNode_Delete(-destTask_Prio′, ′CAP_UNTYPED_CLASS-);ₛ
            ucos_CNode_Delete(-destTask_Prio′, ′CAP_PARTITION_CLASS-);ₛ
            ucos_CNode_Delete(-destTask_Prio′, ′CAP_CHANNEL_CLASS-);ₛ
            ucos_CNode_Delete(-destTask_Prio′, ′CAP_PORT_CLASS-);ₛ
            ucos_CNode_Delete(-destTask_Prio′, ′CAP_BLACKBOARD_CLASS-);ₛ
            ucos_CNode_Delete(-destTask_Prio′, ′CAP_BUFFER_CLASS-);ₛ
            EXIT_CRITICAL;ₛ
            RETURN 〈Int8u〉′CSPACE_NONE_FAULT
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′OS_PRIO_EXIST
    }·.
    

Definition cspace_create_full_impl :=
    Int8u ·cspace_create_full·(⌞destTask_Prio@Int8u⌟)··{
    ⌞pCSpace@CSPACE ∗⌟;
    ENTER_CRITICAL;ₛ
    If(OSCSpacePrioTbl′[destTask_Prio′] ==ₑ 〈CSPACE ∗〉NULL) {
        pCSpace′ =ₑ OSCSpaceFreeList′;ₛ
        OSCSpaceFreeList′ =ₑ OSCSpaceFreeList′→OSCSpaceNext;ₛ
        OSCSpacePrioTbl′[destTask_Prio′] =ₑ pCSpace′;ₛ
        OSCSpaceObjectPointer′[destTask_Prio′] =ₑ ′OBJ_POSITION;ₛ
        pCSpace′→child_num =ₑ ′0;ₛ
        pCSpace′→cnode..guide_num =ₑ ′8;ₛ
        pCSpace′→cnode..slot_num =ₑ ′8;ₛ
        ucos_Grant_Cap(­destTask_Prio′,′CAP_TASK_CLASS,′CAP_TASK_RIGHT­);ₛ
        ucos_Grant_Cap(­destTask_Prio′,′CAP_QUEUE_CLASS,′CAP_QUEUE_RIGHT­);ₛ
        ucos_Grant_Cap(­destTask_Prio′,′CAP_MUTEX_CLASS,′CAP_MUTEX_RIGHT­);ₛ
        ucos_Grant_Cap(­destTask_Prio′,′CAP_SEM_CLASS,′CAP_SEM_RIGHT­);ₛ
        ucos_Grant_Cap(­destTask_Prio′,′CAP_CNODE_CLASS,′CAP_CNODE_RIGHT­);ₛ
        ucos_Grant_Cap(­destTask_Prio′,′CAP_UNTYPED_CLASS,′CAP_UNTYPED_RIGHT­);ₛ
        ucos_Grant_Cap(­destTask_Prio′,′CAP_PARTITION_CLASS,′CAP_PARTITION_RIGHT­);ₛ
        ucos_Grant_Cap(­destTask_Prio′,′CAP_CHANNEL_CLASS,′CAP_PORT_RIGHT­);ₛ
        ucos_Grant_Cap(­destTask_Prio′,′CAP_PORT_CLASS,′CAP_PORT_RIGHT­);ₛ
        ucos_Grant_Cap(­destTask_Prio′,′CAP_BLACKBOARD_CLASS,′CAP_PORT_RIGHT­);ₛ
        ucos_Grant_Cap(­destTask_Prio′,′CAP_BUFFER_CLASS,′CAP_PORT_RIGHT­);ₛ
        EXIT_CRITICAL;ₛ
        RETURN 〈Int8u〉′CSPACE_NONE_FAULT
    };ₛ
    EXIT_CRITICAL;ₛ
    RETURN 〈Int8u〉′OS_PRIO_EXIST
    }·.

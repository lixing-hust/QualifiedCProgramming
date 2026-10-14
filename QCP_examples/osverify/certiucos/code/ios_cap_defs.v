Require Import os_code_defs.
Require Import code_notations.


Definition category_content :ident:=37001%Z.
Definition category_right :ident:=37002%Z.
Definition object_right : ident := 37003%Z.
Definition object_t :ident := 37004%Z.
Definition category :ident := 37005%Z.
Definition object :ident:= 37006%Z.
Definition cap_type :ident:= 37007%Z.
Definition cap_content :ident:= 37008%Z.
Definition slot_type :ident:=37009%Z.
Definition capability :ident:=37010%Z.
Definition guide_num :ident:=37011%Z.
Definition slot_num :ident:=37012%Z.
Definition slots :ident:=37013%Z.
Definition cnode :ident:=37014%Z.
Definition child_num :ident:=37015%Z.
Definition cspace_children :ident:=37016%Z.
Definition OSCSpaceNext :ident:=37017%Z.
Definition destTask_Prio :ident:= 37018%Z.
Definition cap_Class :ident:= 37019%Z.
Definition cap_Right :ident:=37020%Z.
Definition OSCSpacePrioTbl:ident:=37021%Z.
Definition srcTask_Prio:ident:=37022%Z.
Definition func_capability:ident:=37033%Z.
Definition rights :ident:=37044%Z.
Definition pCSpace1:ident:=37045%Z.
Definition pCSpace2:ident:=37046%Z.
Definition cap1:ident:=37047%Z. 
Definition cap2:ident:=37048%Z. 
Definition idx:ident:=37049%Z.
Definition prio :ident:=37050%Z. 
Definition func_object :ident:= 37051%Z.
Definition endPtr :ident:= 37052%Z.
Definition pCSpace :ident:=37053%Z.
Definition i:ident:= 37054%Z. 
Definition OSCSpaceObjectPointer:ident:=37055%Z. 
Definition dest_space :ident:= 37056%Z.
Definition func_capType :ident:=37057%Z.
Definition CapParent :ident:=37058%Z.
Definition index :ident:=37059%Z.
Definition ret :ident:=37060%Z.
Definition taskPrio :ident:=37061%Z.

Definition OSCSpaceCur:ident:=37061%Z.
Definition OSCSpaceList:ident:=37062%Z.
Definition OSCSpaceFreeList:ident:=37603%Z.
Definition TCBCap:ident:= 37604%Z.

(*为了标识符的唯一性，不得不将一些变量改名*)
Definition cap_category := 37300%Z.
Definition cap_object := 37301%Z.
Definition cap := 37302%Z.
Definition cspace := 37303%Z.
Definition content := 37304%Z.
Definition slot := 37305%Z.
Definition cte := 37306%Z.
Definition ucos_Grant_Cap := 37307%Z.
Definition ucos_CNode_Mint := 37308%Z.
Definition ucos_CNode_Copy :=37309%Z.
Definition Get_Obj_Slot := 37310%Z.
Definition ucos_CNode_Move := 37311%Z.
Definition ucos_CNode_Mutate := 37312%Z. 
Definition ucos_CNode_Delete := 37313%Z.
Definition CNode_delete_recursive := 37314%Z.
Definition ucos_CNode_Revoke := 37315%Z. 
Definition grant_cspace_cap := 37316%Z.
Definition user_cnode_mint := 37317%Z.
Definition user_cnode_copy := 37318%Z.

Definition Check_Cap_Type := 37319%Z.
Definition Dummy_ptr := 37320%Z. 
Definition Dummy_int := 37321%Z. 
Definition user_cnode_move := 37322%Z. 
Definition user_cnode_mutate := 37323%Z. 
Definition user_cnode_delete := 37324%Z.
Definition user_cnode_revoke := 37325%Z. 
Definition Get_Obj_Slot_without_critical := 37326%Z.
Definition cspace_create_empty := 37327%Z.
Definition cspace_create_full := 37328%Z.

(*常量值*)
Definition MaxChildNum := 64%Z.
Definition SLOT_NUM :=255%Z.
Definition CAP_CATEGORY_TYPE := 1%Z. 
Definition CAP_OBJECT_TYPE:=2%Z.
Definition CNODE_MINT_FAILURE:=5%Z. 
Definition CNODE_NONE_FAULT := 0%Z.
Definition OS_LOWEST_PRIO := 63%Z. 
Definition OS_PRIO_SELF := 255%Z. 
Definition OS_PRIO_INVALID := 42%Z.
Definition OBJ_POSITION := 17%Z. 
Definition SLOT_NULL_CAP := 0%Z. 
Definition CNODE_COPY_FAILURE := 6%Z.
Definition CNODE_MOVE_FAILURE:=7%Z.
Definition CNODE_MUTATE_FAILURE := 8%Z.
Definition CNODE_DELETE_FAILURE :=9%Z.
Definition CNODE_REVOKE_FAILURE := 10%Z.
Definition CNODE_GRANT_CAP := 64%Z.
Definition CSPACE_NONE_FAULT :=0%Z.
Definition USER_CAPABILITY_NONE := 252%Z.
Definition CNODE_MINT_CAP := 1%Z.
Definition CNODE_COPY_CAP := 2%Z.
Definition CNODE_MINT_SUCCESS := 0%Z.
Definition CAP_TASK_TYPE :=5%Z.
Definition EINVAL := 22%Z.
Definition CAP_FUNCTION_TYPE := 1%Z.
Definition CAP_CHANNEL_CLASS := 16%Z.
Definition CAP_SEM_TYPE:=2%Z. 
Definition CAP_MUTEX_TYPE:=3%Z. 
Definition CAP_Q_TYPE := 4%Z. 
Definition OS_STAT_PRIO := 62%Z.
Definition SLOT_CNODE_CAP:=11%Z.
(* Definition CNODE_COPY_CAP:= 2%Z. *)
Definition CNODE_COPY_SUCCESS := 0%Z.
Definition CNODE_GRANT_FAILURE := 11%Z. 
Definition CNODE_MOVE_SUCCESS := 0%Z. 
Definition CNODE_MUTATE_SUCCESS := 0%Z.
Definition CNODE_DELETE_SUCCESS := 0%Z.
Definition CNODE_REVOKE_SUCCESS := 0%Z. 
Definition CNODE_MOVE_CAP := 4%Z. 
Definition CNODE_MUTATE_CAP := 8%Z.
Definition CNODE_DELETE_CAP := 16%Z.
Definition CNODE_REVOKE_CAP := 32%Z.
Definition SLOT_RANGE_OVERFLOW := 2%Z.

Definition CAP_NULL_CLASS  	:= 0%Z.
Definition CAP_PARTITION_CLASS := 1%Z.
Definition CAP_TASK_CLASS := 2%Z.
Definition CAP_TIME_CLASS := 3%Z.
Definition CAP_MBOX_CLASS := 4%Z.
Definition CAP_QUEUE_CLASS := 5%Z.
Definition CAP_FLAG_CLASS := 6%Z.
Definition CAP_MEM_CLASS := 7%Z.
Definition CAP_MUTEX_CLASS := 8%Z.
Definition CAP_SEM_CLASS := 9%Z.
Definition CAP_PORT_CLASS := 10%Z.
Definition CAP_CNODE_CLASS := 11%Z.
Definition CAP_UNTYPED_CLASS := 12%Z.
Definition CAP_CPUSEM_CLASS := 13%Z.
Definition CAP_BLACKBOARD_CLASS := 14%Z.
Definition CAP_BUFFER_CLASS := 15%Z.

Definition CAP_PARTITION_RIGHT := -1%Z.
Definition CAP_TASK_RIGHT :=-1%Z.
Definition CAP_TIME_RIGHT :=-1%Z.
Definition CAP_MBOX_RIGHT :=-1%Z.
Definition CAP_QUEUE_RIGHT :=-1%Z.
Definition CAP_FLAG_RIGHT :=-1%Z.
Definition CAP_MEM_RIGHT :=-1%Z.
Definition CAP_MUTEX_RIGHT :=-1%Z.
Definition CAP_SEM_RIGHT :=-1%Z.
Definition CAP_PORT_RIGHT :=-1%Z.
Definition CAP_CNODE_RIGHT :=-1%Z.
Definition CAP_UNTYPED_RIGHT :=-1%Z.
Definition CAP_CPUSEM_RIGHT :=-1%Z.

Definition OS_PRIO_EXIST := 40%Z.
Open Scope code_scope.
(* Definition CAP_MAX_EVENTS := 36%Z. 
Definition CAP_USER_MAX_EVENTS :=(OS_MAX_EVENTS-CORENUM*2)%Z. *)

(*这里由于证明框架对于一块内存存储的数据是有类型限制的，所以，category_right和object在一块内存上是有问题
因此这里增加了一个trick, 增加两个虚拟变量使得两个变量不共享一块内存*)
Definition Cap_Category : type := 
    STRUCT cap_category ­{
                        ⌞category_content @ Int32u;   
                        category_right @ Int32u;
                        Dummy_ptr @ (Void ∗)
                        ⌟
                        }­.
Definition Cap_Object : type := 
    STRUCT cap_object ­{
                        ⌞object_right @ Int32u;
                         Dummy_int @ Int32u;
                         object_t @ (Void ∗)⌟
                         }­.
Definition Content : type :=
    UNION content  ­{
                    ⌞category @ Cap_Category;
                    object @ Cap_Object⌟
                    }­.
                    
Definition Cap : type := 
    STRUCT cap ­{
                    ⌞cap_type @ Int32u;
                     cap_content @ Content⌟
                     }­.
Definition Slot : type :=
    STRUCT slot ­{
                    ⌞slot_type @ Int32u;
                     capability @ Cap⌟
                      }­.
Definition Cte : type :=
    STRUCT cte  ­{
                    ⌞guide_num @ Int32u;
                     slot_num @ Int32u;
                     slots @ (Tarray Slot ∘SLOT_NUM)
                    ⌟
                    }­.

Definition CSPACE :type := 
    STRUCT cspace  ­{
                ⌞  cnode @ Cte;
                   child_num @ Int32u;
                   cspace_children @ (Tarray STRUCT cspace ⋆ ∘MaxChildNum);
                   OSCSpaceNext @ STRUCT cspace ⋆;
                   taskPrio@Int32u
                   ⌟
                   }­.
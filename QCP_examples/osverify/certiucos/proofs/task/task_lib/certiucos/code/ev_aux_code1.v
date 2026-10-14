
Require Import os_code_defs1.
Require Import code_notations1.

Open Scope code_scope.

Definition gjb_pos_blk : ident := 1901%Z.
Definition nextpblk : ident := 1902%Z.
Definition posval : ident := 1903%Z.

Definition gjb_pos_blk_t : type :=
  STRUCT gjb_pos_blk ­{
      ⌞
        posval @ Int32u ;  
        nextpblk @ STRUCT gjb_pos_blk ⋆ 
      ⌟ 
    }­.

Definition V_posblk_pos (vl:vallist) := nth_val 0 vl.
Definition V_posblk_next (vl:vallist) := nth_val 1 vl. 

Definition GJB_pos_list : ident := 1911%Z. 

Close Scope code_scope. 

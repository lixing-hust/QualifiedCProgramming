Require Import include_frm.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_inv.

Local Open Scope code_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

(* used for IntPartitionMuxInit *)

Fixpoint set_idm_to_ipm (cnum: nat) (idm: IntrDomMod.map) (ipm: IntPMuxMod.map) : IntPMuxMod.map :=
  match cnum with
  | 0%nat => match IntrDomMod.get idm (Int.repr (Z.of_nat cnum)) with
              | None => ipm
              | Some idmv => (set ipm (Int.repr (Z.of_nat cnum)) idmv)
              end
  | (S cnum') => match IntrDomMod.get idm (Int.repr (Z.of_nat cnum)) with
                  | None => set_idm_to_ipm cnum' idm ipm
                  | Some idmv => set (set_idm_to_ipm cnum' idm ipm) 
                                     (Int.repr (Z.of_nat cnum)) idmv
                  end
  end.

Definition IntPartMux_P n intrvl intpvl' :=
forall i v1 v2, 0 <= i /\ i < n ->
                        nth_val (nat_of_Z i) intrvl = Some v1 ->
                        nth_val (nat_of_Z i) intpvl' = Some v2 ->
                        Some v1 = Some v2.

(* used for InitDnum *)

Fixpoint ksDomains_binAddress_to_Domain2Index (vall1: list domainConfVal) (v2:vallist) (j:nat) : Prop :=
  match vall1 with
  | nil => True
  | (vl, vl', vl'', vl''') :: val'  =>
    (nth_val 3 vl = Some (V$ 0)) /\
     nth_val 0 vl = Some (V$ x) /\
    (nth_val ( Z.to_nat  x) v2 = Some (V$ (Z.of_nat j)) )  /\
      ksDomains_binAddress_to_Domain2Index val' v2 (S j) 
      \/ (
    (nth_val 3 vl <> Some (V$ 0))/\
     ksDomains_binAddress_to_Domain2Index val' v2 j )
end.

Definition nth_domain i (l : list domainConfVal ) :=
  match (nth_error l (nat_of_Z i)) with
    | Some (v0,v1,v2,v3)  => 
           match (nth_val 3 v0) with
                    | Some (Vint32 x) => 
                          match (Int.eq x ($0)) with 
                              | true => None
                              | false => (nth_val 0 v0)
                          end
                    | _ => None
                end
              | _ => None
            end.

Fixpoint max_k i x (l : list domainConfVal )  :=
  match i with
  | 0%nat => 0
  | S i' => 
    match (nth_domain (Z.of_nat  (S i')) l) with
      | Some (Vint32 m) =>
            match (Int.eq m x) with
                | true => (Z.of_nat  (S i'))
                | false => max_k i' x l 
            end
      | _ => max_k i' x l 
    end
end.

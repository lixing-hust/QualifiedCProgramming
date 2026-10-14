Require Import include_frm.
Require Import os_code_defs.
Require Import code_notations.
Require Import sep_auto.
Require Import seplog_tactics.
Require Import seplog_trm_tacs.
Require Import symbolic_lemmas.
Require Import symbolic_execution.
Require Import hoare_assign.
Require Import hoare_conseq.
Require Import math_auto.
Require Import gjb_common.
Require Import pure.
Require Import hoare_forward.
Require Import hoare_tactics.
Require Import ucos_pauto.
Require Import os_inv.
Require Import evauxvar_lemmas.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope code_scope.

Ltac find_ptrstruct_by_block' Hp b :=
  match Hp with
    | ?A ** ?B =>
      match find_ptrstruct_by_block' A b with
        | (some ?m) => constr:(some m)
        | (none ?m) =>
          match find_ptrstruct_by_block' B b with
            | (some ?n) => constr:(some (m + n)%nat)
            | (none ?n) => constr:(none (m + n)%nat)
          end
      end
    | Astruct (b, _) _ _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac find_ptrstruct_by_block Hp b :=
  let x := find_ptrstruct_by_block' Hp b in
  eval compute in x.

Ltac sep_get_lv_array_struct :=
  let Hsat := fresh in
  let Heq:= fresh in
  let Hsat' := fresh in
  match goal with
    | |- ?P ==> Lv (efield (earrayelem (evar ?gident) (evar ?ident)) ?id) @  ?tp1 ==  _ =>
          introv Hsat;
          sep_lifts_trms_in Hsat (Agvarmapsto gident, Alvarmapsto ident, A_dom_lenv);
         match goal with
            | Hsat: ?s |= GV gident @ Tptr ?tp |-> Vptr (?b,?i) **
                              LV ident @ _ |-> Vint32 ?idx ** A_dom_lenv _ ** ?P' 
              |- ?s |= Lv (efield (earrayelem (evar ?gident) (evar ?ident)) ?id) @  ?tp1 ==  _ =>
           (match idx with
                | Int.repr _ => idtac
                | _ => assert (Heq: idx = Int.repr (Int.unsigned idx)) by (rewrite Int.repr_unsigned; auto);
                          sep remember (1::2::3::nil)%nat in Hsat;
                          rewrite Heq in Hsat; 
                          match goal with
                            | Hsat': ?s |= GV gident @ Tptr ?tp |-> Vptr (?b,?i) **
                                  LV ident @ _ |-> Vint32 ?idx ** A_dom_lenv _ ** ?P' 
                                  |-  _ =>
                               subst P'
                          end
              end);
             eapply Info_get_lv_general; [ idtac | .. | eauto];
            [ auto
             | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
             | simpl;auto
             | unfold field_offset; simpl; auto
             | try auto; try apply Int.unsigned_range_2
             | try (apply user_max_events_le; auto)
             | simpl; clear; int auto
             | simpl; clear; int auto]
          end
   end.

  Ltac sep_get_rv_array_struct :=
  let Hsat := fresh in
  let Hf := fresh in
  let Heq := fresh in
  match goal with
  | |- ?P ==> Rv efield (?gident ′ [?ident ′]) ?id @ ?tp1 == _ =>
        introv Hsat; sep_lifts_trms_in Hsat (Agvarmapsto gident, Alvarmapsto ident);
         match goal with
         | Hsat:?s
                |= GV gident @ ?tp ∗ |-> Vptr (?b, ?i) **
                   LV ident @ _ |-> Vint32 ?idx ** ?P'
           |- ?s |= Rv efield (?gident ′ [?ident ′]) ?id @ ?tp1 == _ =>
               match find_ptrstruct_by_block P' b with
               | some ?n => sep lifts (S (S n) :: nil) in Hsat
               end; sep_lifts_trms_in Hsat (Agvarmapsto gident, Alvarmapsto ident);
                eapply struct_array_member_rv;
                [ try symbolic_execution
                | try symbolic_execution
                | try sep lift 3%nat in Hsat;
                   match idx with
                   | $ Z.of_nat ?idx0 =>
                       assert (Heq : Int.unsigned ($ Z.of_nat idx0) = Z.of_nat idx0);
                        [ try apply user_max_events_eq; try auto with zarith |  ]
                   | _ => idtac
                   end; try rewrite Heq; try rewrite Nat2Z.id; eauto
                | match goal with
                  | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
                  end; auto
                | simpl; auto
                | auto
                | auto
                | try apply int_ltu_zero_eq_false
                | match idx with
                  | $ Z.of_nat ?idx0 =>
                      assert (Heq : Int.unsigned ($ Z.of_nat idx0) = Z.of_nat idx0);
                       [ try apply user_max_events_eq; try auto with zarith |  ]
                  | _ => idtac
                  end; try rewrite Heq; try (apply user_max_events_le'; auto);
                   try (apply pos_rgn_comp'; auto)
                | simpl; try apply thirty_two_min_max
                | auto
                | simpl; auto
                | splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
                | unfold id_nth; simpl; auto
                | auto ]
         end
  | Hsat:?s |= ?P
    |- ?s |= Rv efield (?gident ′ [?ident ′]) ?id @ ?tp1 == _ =>
        sep_lifts_trms_in Hsat (Agvarmapsto gident, Alvarmapsto ident);
         match goal with
         | Hsat:?s
                |= GV gident @ ?tp ∗ |-> Vptr (?b, ?i) **
                   LV ident @ _ |-> Vint32 ?idx ** ?P'
           |- ?s |= Rv efield (?gident ′ [?ident ′]) ?id @ ?tp1 == _ =>
               match find_ptrstruct_by_block P' b with
               | some ?n => sep lifts (S (S n) :: nil) in Hsat
               end; sep_lifts_trms_in Hsat (Agvarmapsto gident, Alvarmapsto ident);
                eapply struct_array_member_rv;
                [ try symbolic_execution
                | try symbolic_execution
                | try sep lift 3%nat in Hsat;
                   match idx with
                   | $ Z.of_nat ?idx0 =>
                       assert (Heq : Int.unsigned ($ Z.of_nat idx0) = Z.of_nat idx0);
                        [ try apply user_max_events_eq; try auto with zarith |  ]
                   | _ => idtac
                   end; try rewrite Heq; try rewrite Nat2Z.id; eauto
                | match goal with
                  | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
                  end; auto
                | simpl; auto
                | auto
                | auto
                | try apply int_ltu_zero_eq_false
                | match idx with
                  | $ Z.of_nat ?idx0 =>
                      assert (Heq : Int.unsigned ($ Z.of_nat idx0) = Z.of_nat idx0);
                       [ try apply user_max_events_eq; try auto with zarith |  ]
                  | _ => idtac
                  end; try rewrite Heq; try (apply user_max_events_le'; auto);
                   try (apply pos_rgn_comp'; auto)
                | simpl; try apply thirty_two_min_max
                | auto
                | simpl; auto
                | splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
                | unfold id_nth; simpl; auto
                | auto ]
         end
  end.

 Ltac sep_get_rv_array_struct' :=
  let Hsat := fresh in
  let Hf := fresh in
  let Ht'' := fresh in
  let Hn := fresh in
  match goal with
    | |- ?P ==> Rv efield (ederef (efield (earrayelem (evar ?gident) (evar ?ident)) ?id)) ?id2 @  ?tp1 ==  _ =>
          introv Hsat;
          eapply struct_member_e_rv;
         [ try sep_get_rv_array_struct
             | try sep cancel Astruct; eauto
             | try ((match goal with |- ?tp = Tstruct _ _ => try unfold tp end); eauto)
             | try (simpl;auto)
             | try (simpl;auto)
             | try (intro Ht''; intro Hn; intro Hf; inv Hf)
             | try (intro Ht''; intro Hn; intro Hf; inv Hf)
             | try (intro Ht''; intro Hn; intro Hf; inv Hf)
             | try (unfold id_nth; simpl; auto)
             | try (simpl; auto with zarith)
             | try go
             | try (simpl; auto)]
    |  Hsat: ?s |= ?P |- ?s |= Rv efield (ederef (efield (earrayelem (evar ?gident) (evar ?ident)) ?id)) ?id2 @  ?tp1 ==  _ =>
               eapply struct_member_e_rv;
          [ try sep_get_rv_array_struct
             | try sep cancel Astruct; eauto
             | try ((match goal with |- ?tp = Tstruct _ _ => try unfold tp end); eauto)
             | try (simpl;auto)
             | try (simpl;auto)
             | try (intro Ht''; intro Hn; intro Hf; inv Hf)
             | try (intro Ht''; intro Hn; intro Hf; inv Hf)
             | try (intro Ht''; intro Hn; intro Hf; inv Hf)
             | try (unfold id_nth; simpl; auto)
             | try (simpl; auto with zarith)
             | try go
             | try (simpl; auto)]
   end.

  Ltac hoare_assign_array_struct_part :=
  let s := fresh in
  let H := fresh in
  match goal with
    | |- {| _, _, ?li, _, _, _ |} |- ?ct  {{ ?P }} (sassign (efield (earrayelem (evar ?gident) (evar ?ident)) ?id) ?e2) {{ _ }} =>
         hoare_lifts_trms_pre (Aop, Agvarmapsto gident, Alvarmapsto ident, A_dom_lenv);
         match goal with
            | |- {| _, _, _, _, _, _ |} |- ?ct  {{ <|| _ ||> ** GV gident @ Tptr ?tp |-> Vptr (?b,?i) **
                                                            LV ident @ _ |-> Vint32 ?idx ** A_dom_lenv _ ** ?P' }} _ {{ _ }} =>
            (match find_ptrstruct_by_block P' b with
                      | some ?n => hoare lifts (S (S (S (S n))) :: nil)%list pre
            end);
            hoare_lifts_trms_pre (Aop, Agvarmapsto gident, Alvarmapsto ident, A_dom_lenv);
            try eapply assign_rule_array_struct_aop_general;
            [ try (intro s; split; intro H; try sep cancel Astruct; try rewrite Int.repr_unsigned in *; exact H)
             | try ((match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto)
             | try (simpl;auto)
             | try (unfold field_offset; simpl; auto)
             | try (intros; intro; tryfalse)
             | try (intros; intro; tryfalse)
             | try (intros; intro; tryfalse)
             | try (simpl; auto)
             | try (unfold id_nth; simpl; auto)
             | try (simpl; auto with zarith)
             | try (simpl; auto)
             | try (simpl; auto)
             | idtac
             | try sep_get_lv_array_struct
             | try symbolic execution
             | try (li_sepauto li) ]
            end
  end.

  Ltac hoare_assign_array_struct :=
         hoare_assign_array_struct_part;
         try (match goal with |- assign_type_match ?tp1 _ => 
                    match tp1 with
                          | Tptr _ => apply eq_vptr; simpl; eauto
                          | Tint8 =>  apply eq_int; simpl; auto
                          | Tint16 =>  apply eq_int; simpl; auto
                          | Tint32 =>  apply eq_int; simpl; auto
                          | _ => idtac
                   end
                 end).

  Ltac hoare_assign_array_struct' tp :=
         hoare_assign_array_struct_part;
         try (match goal with |- assign_type_match ?tp1 _ => 
                    match tp1 with
                          | Tptr _ => apply eq_vptr; try instantiate (1:= tp); simpl; eauto
                          | Tint8 =>  apply eq_int; try instantiate (1:= tp); simpl; auto
                          | Tint16 =>  apply eq_int; try instantiate (1:= tp); simpl; auto
                          | Tint32 =>  apply eq_int; try instantiate (1:= tp); simpl; auto
                          | _ => idtac
                   end
                 end).

Ltac unfold_p_local :=
   let H := fresh in
   let Hlg := fresh in
   hoare_lifts_trms_pre p_local;
   unfold p_local at 2; unfold OSLInv at 3; unfold LINV;
   hoare normal pre; hoare_ex_intro;
   hoare_lifts_trms_pre isflag;
   apply pure_split_rule'; introv H; destruct H as (H & Hlg); inverts H;
   hoare_split_pure_all.

Ltac sep_evaux_p_local ct trm :=
  let H := fresh in
  match goal with 
    | |- _ ==> EX lg : list logicvar, p_local _ _ _ ** _ =>
        (introv H; unfold p_local; unfold OSLInv; unfold LINV;
          sep eexists; sep normal; sep eexists; sep split;
          [sep cancel (get_off_addr ct flag_off);
            try_cancel_evaux_asst; sep cancel CurTid;
            sep_lifts_trms_in H trm;
            apply sep_combine_lemmas.PV_separate_rw_frm in H;
            sep cancel trm; sep pauto
           | pure_auto
           | splits; try pauto ])
    end.
    
    
Ltac forward_evaux' ct eq_tp_tac :=
  let h := fresh in
  hoare_lifts_trms_pre Aop; 
    eapply assign_rule';
      [ eq_tp_tac; eauto
      | introv h; split;
         [ eapply symbolic_lemmas.field_asrt_impl_g;
            [ 
            | 
            | sep normal; unfold AOSTCBList in h; sep normal in h; sep destruct h;
               destruct ct; sep cancel (Agvarmapsto OSTCBCur);
               sep_lifts_trms_in h A_dom_lenv;
               eapply symbolic_lemmas.dom_lenv_imp_notin_lenv with (x := OSTCBCur) in h;
               [ sep cancel A_notin_lenv; sep auto | auto ] ]
         | sep
         get
         rv ]
      |  ] .
  
Ltac forward_evloc_assg ct :=
 combine_evaux (get_off_addr ct evloc_off); 
  try (forward_evaux ct ltac:(eapply eq_int) );
 try (forward_evaux' ct ltac:(eapply eq_int) ).
 
  
Ltac hoare_assign_evaux :=
  let s := fresh in
  let H := fresh in
  let Hlg := fresh in
  match goal with
    | |- {| _, _, ?li, _, _, _ |} |- ?ct  {{ ?P }} (sseq (sassign (efield (ederef (evar ?gident)) ?id) ?e2) ?s1) {{ _ }} =>
         match id with
               | __OSTskSemPtr =>
                      try unfold_p_local;
                      (match e2 with
                              | enull => forward_semp_assg_null ct
                              | _ => forward_semp_assg ct
                       end);
                       try go;
                       try (sep_evaux_p_local ct (get_off_addr ct semptr_off));
                       try (match goal with
                               | |- {| _, _, ?li, _, _, _ |} |- ?ct  {{ ?P }} _ {{ _ }} => 
                                   try (eapply backward_rule1;
                                           [ introv H; sep_lifts_trms_in H (get_off_addr ct semptr_off);
                                             apply sep_combine_lemmas.PV_separate_rw_frm in H; eauto
                                           | idtac])
                                end)
               | __OSTskMuxPtr =>
                     try unfold_p_local;
                      (match e2 with
                              | enull => forward_muxp_assg_null ct
                              | _ => forward_muxp_assg ct
                       end);
                       try go;
                       try (sep_evaux_p_local ct (get_off_addr ct muxptr_off));
                       try (match goal with
                               | |- {| _, _, ?li, _, _, _ |} |- ?ct  {{ ?P }} _ {{ _ }} => 
                                   try (eapply backward_rule1;
                                           [ introv H; sep_lifts_trms_in H (get_off_addr ct muxptr_off);
                                             apply sep_combine_lemmas.PV_separate_rw_frm in H; eauto
                                           | idtac])
                                end)
               | __OSTskQPtr =>
                      try unfold_p_local;
                      (match e2 with
                              | enull => forward_mqp_assg_null ct
                              | _ => forward_mqp_assg ct
                       end);
                      try go;
                      try (sep_evaux_p_local ct (get_off_addr ct qptr_off));
                      try (match goal with
                               | |- {| _, _, ?li, _, _, _ |} |- ?ct  {{ ?P }} _ {{ _ }} => 
                                   try (eapply backward_rule1;
                                           [ introv H; sep_lifts_trms_in H (get_off_addr ct qptr_off);
                                             apply sep_combine_lemmas.PV_separate_rw_frm in H; eauto
                                           | idtac])
                                end)
               | __OSTskEvLoc =>
                      try unfold_p_local;
                      forward_evloc_assg ct;
                      try go;
                      try (sep_evaux_p_local ct (get_off_addr ct evloc_off))     ;
                      try (match goal with
                               | |- {| _, _, ?li, _, _, _ |} |- ?ct  {{ ?P }} _ {{ _ }} => 
                                   try (eapply backward_rule1;
                                           [ introv H; sep_lifts_trms_in H (get_off_addr ct evloc_off);
                                             apply sep_combine_lemmas.PV_separate_rw_frm in H; eauto
                                           | idtac])
                                end) 
               | _ => idtac
             end
     | |- {| _, _, ?li, _, _, _ |} |- ?ct  {{ ?P }}  (sassign (efield (ederef (evar ?gident)) ?id) ?e2)  {{ _ }} =>
         match id with
               | __OSTskEvLoc =>
                      try unfold_p_local  ;
                      forward_evloc_assg ct;
                      try go   ;
                      try (sep_evaux_p_local ct (get_off_addr ct evloc_off))    ;
                      try (match goal with
                               | |- {| _, _, ?li, _, _, _ |} |- ?ct  {{ ?P }} _ {{ _ }} => 
                                   try (eapply backward_rule1;
                                           [ introv H; sep_lifts_trms_in H (get_off_addr ct evloc_off)  ;
                                             apply sep_combine_lemmas.PV_separate_rw_frm in H; eauto 
                                           | idtac])
                                end) 
               | _ => idtac
             end
    end.

Ltac fold_evaux :=
  let Hsat := fresh in
  eapply backward_rule1;
   [ introv Hsat; eapply llsegevaux_merge2_frm;
      [ sep cancel llsegevaux; eapply llsegevaux_merge_hd;
         [ sep cancel evaux_node; sep cancel llsegevaux; eauto
         | eauto
         | eauto
         | eauto ]
      | eauto
      | eauto ]
   |  ].

   Ltac fold_evaux_mux vptr :=
          let Hsat:= fresh in
                eapply backward_rule1;
               [ introv Hsat;
                  eapply llsegevaux_merge2_frm;
                  [ sep cancel llsegevaux;
                     eapply llsegevaux_merge_hd with (v2:= vptr);
                     [ unfold evaux_node; sep cancel llsegevaux;
                        sep cancel evloc_off; sep cancel muxptr_off; sep cancel semptr_off; sep cancel qptr_off;
                        simpl rule_type_val_match at 2;
                        do 3 try (sep cancel rule_type_val_match);
                         sep split; eauto
                        | eauto
                        | eauto
                        | eapply join_lib.join_sig_set; eauto   ]
                    | eauto
                    | eapply EvAuxPtrMod.joinsig_set_set; eauto ]
                | idtac].

    Ltac fold_evaux_sem vptr :=
          let Hsat:= fresh in
                eapply backward_rule1;
               [ introv Hsat;
                  eapply llsegevaux_merge2_frm;
                  [ sep cancel llsegevaux;
                     eapply llsegevaux_merge_hd with (v3:= vptr);
                     [ unfold evaux_node; sep cancel llsegevaux;
                        sep cancel evloc_off; sep cancel muxptr_off; sep cancel semptr_off; sep cancel qptr_off;
                        simpl rule_type_val_match at 3;
                        do 3 try (sep cancel rule_type_val_match);
                         sep split; eauto
                        | eauto
                        | eauto
                        | eapply join_lib.join_sig_set; eauto   ]
                    | eauto
                    | eapply EvAuxPtrMod.joinsig_set_set; eauto ]
                | idtac].

    Ltac fold_evaux_q vptr :=
          let Hsat:= fresh in
                eapply backward_rule1;
               [ introv Hsat;
                  eapply llsegevaux_merge2_frm;
                  [ sep cancel llsegevaux;
                     eapply llsegevaux_merge_hd with (v4:= vptr);
                     [ unfold evaux_node; sep cancel llsegevaux;
                        sep cancel evloc_off; sep cancel muxptr_off; sep cancel semptr_off; sep cancel qptr_off;
                        simpl rule_type_val_match at 4;
                        do 3 try (sep cancel rule_type_val_match);
                         sep split; eauto
                        | eauto
                        | eauto
                        | eapply join_lib.join_sig_set; eauto   ]
                    | eauto
                    | eapply EvAuxPtrMod.joinsig_set_set; eauto ]
                | idtac].

    Ltac fold_evaux_loc vloc :=
          let Hsat:= fresh in
                eapply backward_rule1;
               [ introv Hsat;
                  eapply llsegevaux_merge2_frm;
                  [ sep cancel llsegevaux;
                     eapply llsegevaux_merge_hd with (v1:= vloc);
                     [ unfold evaux_node; sep cancel llsegevaux;
                        sep cancel evloc_off; sep cancel muxptr_off; sep cancel semptr_off; sep cancel qptr_off;
                        simpl rule_type_val_match at 1;
                        do 3 try (sep cancel rule_type_val_match);
                         sep split; eauto
                        | eauto
                        | eapply join_lib.join_sig_set; eauto
                        | eauto   ]
                    | eapply EvAuxLocMod.joinsig_set_set; eauto
                    | eauto ]
                | idtac].

   Ltac fold_evaux_mux_loc vloc vptr :=
          let Hsat:= fresh in
                eapply backward_rule1;
               [ introv Hsat;
                  eapply llsegevaux_merge2_frm;
                  [ sep cancel llsegevaux;
                     eapply llsegevaux_merge_hd with (v1:= vloc) (v2:= vptr);
                     [ unfold evaux_node; sep cancel llsegevaux;
                        sep cancel evloc_off; sep cancel muxptr_off; sep cancel semptr_off; sep cancel qptr_off;
                        simpl rule_type_val_match at 2;
                        do 3 try (sep cancel rule_type_val_match);
                         sep split; eauto
                        | eauto
                        | eapply join_lib.join_sig_set; eauto
                        | eapply join_lib.join_sig_set; eauto   ]
                    | eapply EvAuxLocMod.joinsig_set_set; eauto
                    | eapply EvAuxPtrMod.joinsig_set_set; eauto ]
                | idtac].

    Ltac fold_evaux_sem_loc vloc vptr :=
          let Hsat:= fresh in
                eapply backward_rule1;
               [ introv Hsat;
                  eapply llsegevaux_merge2_frm;
                  [ sep cancel llsegevaux;
                     eapply llsegevaux_merge_hd with (v1:= vloc) (v3:= vptr);
                     [ unfold evaux_node; sep cancel llsegevaux;
                        sep cancel evloc_off; sep cancel muxptr_off; sep cancel semptr_off; sep cancel qptr_off;
                        simpl rule_type_val_match at 3;
                        do 3 try (sep cancel rule_type_val_match);
                         sep split; eauto
                        | eauto
                        | eapply join_lib.join_sig_set; eauto
                        | eapply join_lib.join_sig_set; eauto   ]
                    | eapply EvAuxLocMod.joinsig_set_set; eauto
                    | eapply EvAuxPtrMod.joinsig_set_set; eauto ]
                | idtac].

    Ltac fold_evaux_q_loc vloc vptr :=
          let Hsat:= fresh in
                eapply backward_rule1;
               [ introv Hsat;
                  eapply llsegevaux_merge2_frm;
                  [ sep cancel llsegevaux;
                     eapply llsegevaux_merge_hd with (v1:= vloc) (v4:= vptr);
                     [ unfold evaux_node; sep cancel llsegevaux;
                        sep cancel evloc_off; sep cancel muxptr_off; sep cancel semptr_off; sep cancel qptr_off;
                        simpl rule_type_val_match at 4;
                        do 3 try (sep cancel rule_type_val_match);
                         sep split; eauto
                        | eauto
                        | eapply join_lib.join_sig_set; eauto
                        | eapply join_lib.join_sig_set; eauto   ]
                    | eapply EvAuxLocMod.joinsig_set_set; eauto
                    | eapply EvAuxPtrMod.joinsig_set_set; eauto ]
                | idtac].

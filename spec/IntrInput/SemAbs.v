(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Abstract Semantics. *)

Set Implicit Arguments.

Require Import Morphisms.
Require Import List ZArith.
Require Import Monad VocabA Syn TStr DLat DPow DMap DStr DItv
        UserInputType Global Fold.
Require Import DomArrayBlk DomBasic DomAbs DomIntr DomMem SemMem SemEval SemPrune.

Local Open Scope Z.
Local Open Scope sumbool.

Axiom str_realloc : string_t.
Axiom str_strlen : string_t.
Extract Constant str_realloc => """realloc""".
Extract Constant str_strlen => """strlen""".

Module SMProcLoc := SetMap Proc PowProc Loc PowLoc.

Load RunType.

Module Run (Import M : Monad) (MB : MemBasic M) <: RUN M MB.

Module Import SemMem := SemMem.Make M MB.

Module Import SemEval := SemEval.Make M MB.

Module Import SemPrune := SemPrune.Make M MB.

Module BJProcMem := BigJoinM M Proc PowProc Mem.

Section Run.

Variable mode : update_mode.

Variable (g : G.t).

Variable (node : InterNode.t).

Let pid : pid_t := InterNode.get_pid node.

Definition eval := SemEval.eval mode.

Definition mem_lookup k m := mem_lookup k m.

Definition mem_update k v m := mem_update mode g k v m.

Definition mem_wupdate k v m := mem_wupdate mode k v m.

Definition call_name (e : exp) : option pid_t :=
  match e with
  | Lval (lval_intro (VarLhost f _) NoOffset _) _ => Some f
  | _ => None
  end.

Definition is_irq_intrinsic_name (f : pid_t) : bool :=
  if is_enable_irq f then true else
  if is_disable_irq f then true else false.

Definition get_intr (m : Mem.t) : M.m Intr.t :=
  do v <- mem_lookup (PowLoc.singleton loc_of_intr_state) m ;
  let intr := intr_of_val v in
  if Intr.eq_dec intr Intr.bot then ret Intr.Enabled else ret intr.

Definition set_intr (intr : Intr.t) (m : Mem.t) : M.m Mem.t :=
  SemMem.add loc_of_intr_state (val_of_intr intr) m.

Definition run_irq_intrinsic (f : pid_t) (m : Mem.t) : M.m Mem.t :=
  if is_enable_irq f then set_intr Intr.Enabled m else
  if is_disable_irq f then set_intr Intr.Disabled m else ret m.

Definition has_irq_handler : bool :=
  existsb is_irq_handler (InterCfg.pidsof (G.icfg g)).

Definition irq_havoc_val (l : Loc.t) (v : Val.t) : Val.t :=
  if Loc.eq_dec l loc_of_intr_state then modify_intr v Intr.Top
  else modify_itv v Itv.top.

Definition irq_closure (m : Mem.t) : M.m Mem.t :=
  let havoc_loc l v acc_m :=
      do acc <- acc_m ;
      SemMem.weak_add mode l (irq_havoc_val l v) acc in
  do m <- Mem.foldi havoc_loc m (ret m) ;
  SemMem.weak_add mode loc_of_intr_state (val_of_intr Intr.Top) m.

Definition apply_irq_closure (m : Mem.t) : M.m Mem.t :=
  if is_irq_handler pid then ret m else
  if has_irq_handler then
    do intr <- get_intr m ;
    if Intr.is_disabled intr then ret m else
    if Intr.may_enabled intr then irq_closure m else ret m
  else ret m.

Definition update_rets (callees : PowProc.t) (ret_opt : option lval)
           (m : Mem.t) : M.m Mem.t :=
  do ret_locs <- match ret_opt with
               | None => ret PowLoc.bot
               | Some ret_lv => SemEval.eval_lv mode node ret_lv m
             end ;
  let callees_locs := SMProcLoc.map loc_of_proc callees in
  mem_wupdate callees_locs ret_locs m.

Definition external_value (a : Allocsite.t) : Val.t :=
  ( Itv.top
  , PowLoc.singleton (loc_of_allocsite a)
  , ArrayBlk.extern a
  , PowProc.bot
  , Intr.bot).

Definition run_realloc (ret_lv : lval) (vs : list Val.t) (m : Mem.t)
: M.m Mem.t :=
  match vs with
  | _ :: size_v :: _ =>
    do lv <- SemEval.eval_lv mode node ret_lv m ;
    mem_wupdate lv (SemEval.eval_alloc' node size_v) m
  | _ => ret m
  end.

Definition run_strlen (ret_lv : lval) (m : Mem.t) : M.m Mem.t :=
  do lv <- SemEval.eval_lv mode node ret_lv m ;
  mem_wupdate lv Itv.zero_pos m.

Definition set_ext_allocsite (ret_lv : lval) (allocsite : Allocsite.t)
           (m : Mem.t) : M.m Mem.t :=
  let ext_v := external_value allocsite in
  do lv <- SemEval.eval_lv mode node ret_lv m ;
  do m <- mem_wupdate lv ext_v m ;
  mem_wupdate (PowLoc.singleton (loc_of_allocsite allocsite)) ext_v m.

Definition run_undef_funcs (ret_opt : option lval) (ext : pid_t)
           (vs : list Val.t) (m : Mem.t) : M.m Mem.t :=
  match ret_opt with
  | None => ret m
  | Some ret_lv =>
    if DStr.eq_dec ext str_realloc then run_realloc ret_lv vs m else
    if DStr.eq_dec ext str_strlen then run_strlen ret_lv m else
      set_ext_allocsite ret_lv (allocsite_of_ext (Some ext)) m
  end.

Definition run_base (cmd : cmd) (m : Mem.t) : M.m Mem.t :=
  match cmd with
  | Cset (lval_intro (VarLhost x is_global) NoOffset _) e _ =>
    let lv := SemEval.eval_var node x is_global in
    do v <- eval node e m ;
    mem_update lv v m
  | Cset l e _ =>
    do lv <- SemEval.eval_lv mode node l m ;
    do v <- eval node e m ;
    mem_wupdate lv v m
  | Cexternal l _ =>
    set_ext_allocsite l (allocsite_of_ext None) m
  | Calloc l a _ =>
    do lv <- SemEval.eval_lv mode node l m ;
    do v <- SemEval.eval_alloc mode node a m ;
    mem_wupdate lv v m
  | Csalloc l s _ =>
    let allocsite := allocsite_of_node node in
    let pow_loc := PowLoc.singleton (loc_of_allocsite allocsite) in
    do lv <- SemEval.eval_lv mode node l m ;
    do m <- mem_wupdate pow_loc (eval_string s) m ;
    mem_wupdate lv (eval_string_loc s allocsite pow_loc) m
  | Cfalloc l name _ =>
    do lv <- SemEval.eval_lv mode node l m ;
    mem_wupdate lv (PowProc.singleton name : PowProc.t) m
  | Cassume e _ => prune g mode node e m
  | Ccall ret_opt f args _ =>
    match call_name f with
    | Some fname =>
      if is_irq_intrinsic_name fname then run_irq_intrinsic fname m else
        do vs <- SemEval.eval_list mode node args m ;
        match G.is_undef_e f g with
        | Some fname =>
          run_undef_funcs ret_opt fname vs m
        | None =>
          do f_v <- eval node f m ;
          let fs := powProc_of_val f_v in
          do m <- update_rets fs ret_opt m ;
          BJProcMem.weak_big_join (bind_args mode g vs) fs (ret m)
        end
    | None =>
      do vs <- SemEval.eval_list mode node args m ;
      match G.is_undef_e f g with
      | Some fname =>
        run_undef_funcs ret_opt fname vs m
      | None =>
        do f_v <- eval node f m ;
        let fs := powProc_of_val f_v in
        do m <- update_rets fs ret_opt m ;
        BJProcMem.weak_big_join (bind_args mode g vs) fs (ret m)
      end
    end
  | Creturn ret_opt _ =>
    match ret_opt with
    | None => ret m
    | Some e =>
      do v <- eval node e m ;
      do ret_loc <- mem_lookup (PowLoc.singleton (loc_of_proc pid)) m ;
      mem_wupdate (deref_of_val ret_loc) v m
    end
  | Casm _
  | Cskip _ => ret m
  end.

Definition run (cmd : cmd) (m : Mem.t) : M.m Mem.t :=
  do m <- run_base cmd m ;
  apply_irq_closure m.

End Run.

End Run.

Local Close Scope sumbool.
Local Close Scope Z.

Load RunInst.

(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Set Implicit Arguments.

Require Import Morphisms.
Require Import UserInputType UserProofType UserInput.
Require Import DomArrayBlk DomIntr.
Require Import VocabA vgtac Monad.
Require GenFunc.
Require Import DItv.

Include Input.
Include GenFunc.Make.

Definition Var_g (x : DomCon.Var.t) : Var.t :=
  match x with
  | DomCon.Var.Inl gx => Var.Inl gx
  | DomCon.Var.Inr (_, f, lx) => Var.Inr (f, lx)
  end.

Definition Allocsite_g (a : DomCon.Allocsite.t) : Allocsite.t :=
  match a with
  | DomCon.Allocsite.Inl n => Allocsite.Inl n
  | DomCon.Allocsite.Inr (DomCon.ExtAllocsite.Inl f) =>
    Allocsite.Inr (ExtAllocsite.Inl f)
  | DomCon.Allocsite.Inr (DomCon.ExtAllocsite.Inr f) =>
    Allocsite.Inr (ExtAllocsite.Inr f)
  end.

Definition VarRegion_g (vr : DomCon.VarRegion.t) : VarAllocsite.t :=
  match vr with
  | DomCon.VarRegion.Inl x => VarAllocsite.Inl (Var_g x)
  | DomCon.VarRegion.Inr (_, a, _) => VarAllocsite.Inr (Allocsite_g a)
  end.

Fixpoint Fields_g (fs : DomCon.Fields.t) : Fields.t :=
  match fs with
  | DomCon.Fields.nil => Fields.nil
  | DomCon.Fields.cons f tl => Fields.cons f (Fields_g tl)
  end.

Definition Loc_g (l : DomCon.Loc.t) : Loc.t :=
  let (vr, fs) := l in
  Loc.Inl (VarRegion_g vr, Fields_g fs).

Definition Itv_g := Itv.gamma.

Inductive ArrayBlk_g' : DomCon.Region.t -> ArrayBlk.t -> Prop :=
| ArrayBlk_g_intro :
    forall s a o sz st o' sz' st' ab
           (Ho : Itv_g o o') (Hsz : Itv_g sz sz' ) (Hst : Itv_g st st')
           (Hab : ArrayBlk.find (Allocsite_g a) ab = (o', sz', st')),
      ArrayBlk_g' (s, a, (o, sz, st)) ab.

Definition ArrayBlk_g := ArrayBlk_g'.

Inductive Val_g' : DomCon.val_t -> Val.t -> Prop :=
| Val_g_z :
    forall z i ls ab ps intr (Hz : Itv_g z i),
      Val_g' (inl (inl z)) (i, ls, ab, ps, intr)
| Val_g_loc :
    forall l i ls ab ps intr (Hl : PowLoc.mem (Loc_g l) ls = true),
      Val_g' (inl (inr l)) (i, ls, ab, ps, intr)
| Val_g_ab :
    forall r i ls ab ps intr (Hl : ArrayBlk_g r ab),
      Val_g' (inl (inr (DomCon.VarRegion.Inr r, DomCon.Fields.nil)))
            (i, ls, ab, ps, intr)
| Val_g_proc :
    forall p i ls ab ps intr (Hp : PowProc.mem p ps = true),
      Val_g' (inr p) (i, ls, ab, ps, intr).

Definition Val_g := Val_g'.

Definition SProc_g (f : DomCon.Proc.t) : Loc.t := Loc.Inr f.

Axiom val_g_monotone : monotone Val.le Val_g.

Axiom prop_approx_one_loc :
  forall g l (Hl: approx_one_loc g l = true)
     m (Hm : SemCon.wf_non_rec_mem g m)
     l1 (Hl1: Loc.eq (Loc_g l1) l) (Hml1 : DomCon.M.In l1 m)
     l2 (Hl2: Loc.eq (Loc_g l2) l) (Hml2 : DomCon.M.In l2 m),
    DomCon.Loc.eq l1 l2.

Load MemGCommon.

Axiom correct_run :
  forall g step cn cmd con_s con_s' abs_m abs_m'
    (Hmem_g : Mem_g con_s abs_m)
    (HCon : SemCon.Run g step cn cmd con_s con_s')
    (HAbs : abs_m' = run_only Strong g cn cmd abs_m),
    Mem_g con_s' abs_m'.

Load VeqCommon.

Axiom run_only_access_same :
  forall g cn cmd m,
    veq (run_only Strong g cn cmd m) (run_access Strong g cn cmd m).

Axiom run_access_sound :
  forall g cn cmd, aeqm1 (run_access Strong g cn cmd).

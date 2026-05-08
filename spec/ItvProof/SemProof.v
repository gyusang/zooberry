(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Set Implicit Arguments.

Require Import Morphisms.
Require Import ZArith.
Require Import DItv.
Require Import DomArrayBlk.
Require Import UserInputType.
Require Import UserProofType.
Require Import UserInput.
Require GenFunc.
Require Import VocabA.
Require Import vgtac.
Require Import Monad.
Require Import Fold.
Require Import Lia.

Include Input.
Include GenFunc.Make.

Definition Var_g (x : DomCon.Var.t) : Var.t :=
  match x with
  | DomCon.Var.Inl gx => Var.Inl gx
  | DomCon.Var.Inr (_, f, lx) => Var.Inr (f, lx)
  end.

Lemma var_g_mor : Proper (DomCon.Var.eq ==> Var.eq) Var_g.
Proof.
inversion 1.
- by constructor.
- destruct x' as [[n1 f1] x1], y' as [[n2 f2] y2]. simpl in Heq.
  constructor. tauto.
Qed.

Definition Allocsite_g (a : DomCon.Allocsite.t) : Allocsite.t :=
  match a with
  | DomCon.Allocsite.Inl n => Allocsite.Inl n
  | DomCon.Allocsite.Inr (DomCon.ExtAllocsite.Inl f) =>
    Allocsite.Inr (ExtAllocsite.Inl f)
  | DomCon.Allocsite.Inr (DomCon.ExtAllocsite.Inr f) =>
    Allocsite.Inr (ExtAllocsite.Inr f)
  end.

Definition allocsite_g_mor :
  Proper (DomCon.Allocsite.eq ==> Allocsite.eq) Allocsite_g.
Proof.
inversion 1.
- constructor. tauto.
- inversion Heq.
  + constructor. constructor. by auto.
  + constructor. constructor. by auto.
Qed.

Definition VarRegion_g (vr : DomCon.VarRegion.t) : VarAllocsite.t :=
  match vr with
  | DomCon.VarRegion.Inl x => VarAllocsite.Inl (Var_g x)
  | DomCon.VarRegion.Inr (_, a, _) => VarAllocsite.Inr (Allocsite_g a)
  end.

Lemma varregion_g_mor :
  Proper (DomCon.VarRegion.eq ==> VarAllocsite.eq) VarRegion_g.
Proof.
inversion 1.
- constructor. by apply var_g_mor.
- destruct x' as [[n1 a1] [[o1 s1] st1]], y' as [[n2 a2] [[o2 s2] st2]].
  simpl in *.
  constructor. apply allocsite_g_mor. by apply Heq.
Qed.

Fixpoint Fields_g (fs : DomCon.Fields.t) : Fields.t :=
  match fs with
  | DomCon.Fields.nil => Fields.nil
  | DomCon.Fields.cons f tl => Fields.cons f (Fields_g tl)
  end.

Lemma fields_g_mor :
  Proper (DomCon.Fields.eq ==> Fields.eq) Fields_g.
Proof.
unfold Fields.eq. induction DNList.size.
- intros f1 f2 Hf. apply Fields.eq_zero.
- induction 1.
  + apply Fields.eq_nil.
  + apply Fields.eq_cons; [by auto|by apply IHn].
Qed.

Definition Loc_g (l : DomCon.Loc.t) : Loc.t :=
  let (vr, fs) := l in
  Loc.Inl (VarRegion_g vr, Fields_g fs).

Lemma loc_g_mor : Proper (DomCon.Loc.eq ==> Loc.eq) Loc_g.
Proof.
intros [vr1 f1] [vr2 f2] Hl. inversion Hl. constructor. simpl in *; split.
- by apply varregion_g_mor.
- by apply fields_g_mor.
Qed.

Inductive ArrayBlk_g' : DomCon.Region.t -> ArrayBlk.t -> Prop :=
| ArrayBlk_g_intro :
    forall step a o sz st ab io is it
      (Hfind : ArrayBlk.find (Allocsite_g a) ab = ArrInfo.make io is it)
      (Ho : Itv.gamma o io)
      (Hsz : Itv.gamma sz is)
      (Hst : Itv.gamma st it),
      ArrayBlk_g' (step, a, (o, sz, st)) ab.

Definition ArrayBlk_g := ArrayBlk_g'.

Inductive Val_g' : DomCon.val_t -> Val.t -> Prop :=
| Val_g_z :
    forall z i ls ab ps (Hi : Itv.gamma z i),
      Val_g' (inl (inl z)) (i, ls, ab, ps)
| Val_g_loc :
    forall l i ls ab ps (Hl : PowLoc.mem (Loc_g l) ls = true),
      Val_g' (inl (inr l)) (i, ls, ab, ps)
| Val_g_ab :
    forall r i ls ab ps (Hl : ArrayBlk_g r ab),
      Val_g' (inl (inr (DomCon.VarRegion.Inr r, DomCon.Fields.nil)))
             (i, ls, ab, ps)
| Val_g_proc :
    forall p i ls ab ps (Hp : PowProc.mem p ps = true),
      Val_g' (inr p) (i, ls, ab, ps)
.

Definition Val_g := Val_g'.

(** Abstraction of Proc.t in DomCon.stack1. *)
Definition SProc_g (f : DomCon.Proc.t) : Loc.t := Loc.Inr f.

Lemma arrayBlk_g_monotone : monotone ArrayBlk.le ArrayBlk_g.
Proof.
intros r x y Hx Hle. inversion Hx; subst.
specialize (Hle (Allocsite_g a)). rewrite Hfind in Hle.
remember (ArrayBlk.find (Allocsite_g a) y) as info.
destruct info as [[io' is'] it'].
destruct Hle as [[Hio His] Hit].
symmetry in Heqinfo.
eapply ArrayBlk_g_intro; [by apply Heqinfo| | |].
- eapply Itv.gamma_monotone; [by apply Ho|by apply Hio].
- eapply Itv.gamma_monotone; [by apply Hsz|by apply His].
- eapply Itv.gamma_monotone; [by apply Hst|by apply Hit].
Qed.

Lemma val_g_monotone : monotone Val.le Val_g.
Proof.
intros v [[[i ls] ab] ps] [[[i' ls'] ab'] ps'] Hx Hle.
unfold Val.le, Val.E3.le, Val.E2.le in Hle; simpl in Hle.
destruct Hle as [[[Hi Hls] Hab] Hps].
inversion Hx; subst.
- apply Val_g_z. eapply Itv.gamma_monotone; [by apply Hi0|by apply Hi].
- apply Val_g_loc. by apply PowLoc.le_mem_true with ls.
- apply Val_g_ab. by eapply arrayBlk_g_monotone; eauto.
- apply Val_g_proc. by apply PowProc.le_mem_true with ps.
Qed.

Lemma val_g_mor : Proper (Logic.eq ==> Val.eq ==> Basics.impl) Val_g.
Proof.
intros v1 v2 Hv v1' v2' Hv'; intros Hvalg.
eapply val_g_monotone; [rewrite <- Hv; by apply Hvalg|by apply Val.le_refl].
Qed.

Lemma var_g_eq1 :
  forall x1 x2 x (Heq1 : Var.eq (Var_g x1) (Var.Inl x))
     (Heq2 : Var.eq (Var_g x2) (Var.Inl x)),
    DomCon.Var.eq x1 x2.
Proof.
i. unfold Var_g in *.
destruct x1 as [x1|[[? ?] ?]]; [|by inversion Heq1].
destruct x2 as [x2|[[? ?] ?]]; [|by inversion Heq2].
inversion_clear Heq1; inversion_clear Heq2. subst.
by apply DomCon.Var.eq_refl.
Qed.

Lemma var_g_eq2 g :
  forall m (Hm : SemCon.wf_non_rec_mem g m)
     f (Hf : Global.G.is_rec f g = false)
     x1 fs1 x2 fs2 x
     (Hml1 : DomCon.M.In (elt:=DomCon.val_t) (DomCon.VarRegion.Inl x1, fs1) m)
     (Hml2 : DomCon.M.In (elt:=DomCon.val_t) (DomCon.VarRegion.Inl x2, fs2) m)
     (Heq1 : Var.eq (Var_g x1) (Var.Inr (f, x)))
     (Heq2 : Var.eq (Var_g x2) (Var.Inr (f, x))),
    DomCon.Var.eq x1 x2.
Proof.
i. unfold Var_g in *.
destruct x1 as [x1|[[? ?] ?]]; [by inversion Heq1|].
destruct x2 as [x2|[[? ?] ?]]; [by inversion Heq2|].
inversion_clear Heq1; inversion_clear Heq2; simpl in *.
destruct Heq as [Hf1 Hx1], Heq0 as [Hf2 Hx2]. subst.
constructor; s.
split; [|by auto]. split; [|by auto].
eapply Hm; [by apply Hf|by apply Hml1|by apply Hml2].
Qed.

Lemma varregion_g_eq1 :
  forall vr1 vr2 x
     (Hveq1 : VarAllocsite.eq (VarRegion_g vr1) (VarAllocsite.Inl (Var.Inl x)))
     (Hveq2 : VarAllocsite.eq (VarRegion_g vr2) (VarAllocsite.Inl (Var.Inl x))),
    DomCon.VarRegion.eq vr1 vr2.
Proof.
i. unfold VarRegion_g in *.
destruct vr1 as [x1|[[? ?] ?]]; [|by inversion Hveq1].
destruct vr2 as [x2|[[? ?] ?]]; [|by inversion Hveq2].
inversion_clear Hveq1; inversion_clear Hveq2.
constructor. eapply var_g_eq1; [by apply Heq|by apply Heq0].
Qed.

Lemma varregion_g_eq2 g :
  forall m (Hm : SemCon.wf_non_rec_mem g m)
     f (Hf : Global.G.is_rec f g = false)
     vr1 fs1 (Hml1 : DomCon.M.In (elt:=DomCon.val_t) (vr1, fs1) m)
     vr2 fs2 (Hml2 : DomCon.M.In (elt:=DomCon.val_t) (vr2, fs2) m)
     x
     (Hveq1 :
        VarAllocsite.eq (VarRegion_g vr1) (VarAllocsite.Inl (Var.Inr (f, x))))
     (Hveq2 :
        VarAllocsite.eq (VarRegion_g vr2) (VarAllocsite.Inl (Var.Inr (f, x)))),
    DomCon.VarRegion.eq vr1 vr2.
Proof.
i. unfold VarRegion_g in *.
destruct vr1 as [x1|[[? ?] ?]]; [|by inversion Hveq1].
destruct vr2 as [x2|[[? ?] ?]]; [|by inversion Hveq2].
inversion_clear Hveq1; inversion_clear Hveq2.
constructor. eapply var_g_eq2
; [ by apply Hm | by apply Hf | by apply Hml1 | by apply Hml2
  | by apply Heq | by apply Heq0 ].
Qed.

Lemma fields_g_nil' :
  forall f n (Hn : n > 0) (Hf : Fields.eq' n (Fields_g f) Fields.nil),
    f = DomCon.Fields.nil.
Proof.
destruct n; [by inversion 1|i].
destruct f; [reflexivity|].
simpl in Hf. by inversion Hf.
Qed.

Lemma fields_g_nil :
  forall f (Hf : Fields.eq (Fields_g f) Fields.nil),
    f = DomCon.Fields.nil.
Proof.
intros. eapply fields_g_nil'; [|by apply Hf].
unfold DNList.size. lia.
Qed.

Lemma prop_approx_one_loc :
  forall g l (Hl: approx_one_loc g l = true)
     m (Hm : SemCon.wf_non_rec_mem g m)
     l1 (Hl1: Loc.eq (Loc_g l1) l) (Hml1 : DomCon.M.In l1 m)
     l2 (Hl2: Loc.eq (Loc_g l2) l) (Hml2 : DomCon.M.In l2 m),
    DomCon.Loc.eq l1 l2.
Proof.
i. unfold approx_one_loc in Hl.
destruct l as [[[[x|[f x]]|a] fs]|p]; [| |discriminate|discriminate].
- unfold Loc_g in *. destruct l1 as [vr1 fs1], l2 as [vr2 fs2].
  inversion_clear Hl1; inversion_clear Hl2. simpl in Heq, Heq0.
  destruct Heq as [Hveq1 Hfs1], Heq0 as [Hveq2 Hfs2].
  constructor; s.
  + eapply varregion_g_eq1; [by apply Hveq1|by apply Hveq2].
  + destruct fs; [|discriminate].
    rewrite (fields_g_nil _ Hfs1), (fields_g_nil _ Hfs2). constructor.
- unfold Loc_g in *. destruct l1 as [vr1 fs1], l2 as [vr2 fs2].
  inversion_clear Hl1; inversion_clear Hl2. simpl in Heq, Heq0.
  destruct Heq as [Hveq1 Hfs1], Heq0 as [Hveq2 Hfs2].
  constructor; s.
  + destruct fs; [|discriminate].
    eapply varregion_g_eq2
    ; [ by apply Hm | apply Bool.negb_true_iff; by apply Hl
      | by apply Hml1 | by apply Hml2 | by apply Hveq1 | by apply Hveq2 ].
  + destruct fs; [|discriminate].
    rewrite (fields_g_nil _ Hfs1), (fields_g_nil _ Hfs2). constructor.
Qed.

Inductive Loc_opt_g : option DomCon.Loc.t -> PowLoc.t -> Prop :=
| Loc_opt_g_none : forall l', Loc_opt_g None l'
| Loc_opt_g_some :
    forall l l' (Hv : PowLoc.mem (Loc_g l) l' = true), Loc_opt_g (Some l) l'.

Import RunOnly RunOnly.SemMem RunOnly.SemEval.

Load MemGCommon.
Load MemPfCommon.

Local Open Scope Z.
Local Open Scope sumbool.

Lemma val_g_z_inv :
  forall z i ls ab ps,
    Val_g (DomCon.val_of_z z) (i, ls, ab, ps) -> Itv.gamma z i.
Proof.
intros. inversion H; subst; by auto.
Qed.

Lemma val_g_z_gamma :
  forall z av (Hv : Val_g (DomCon.val_of_z z) av),
    Itv.gamma z (itv_of_val av).
Proof.
intros z [[[i ls] ab] ps] Hv. exact (val_g_z_inv Hv).
Qed.

Lemma val_g_z_itv_non_bot :
  forall z av (Hv : Val_g (DomCon.val_of_z z) av),
    ~ Itv.eq (itv_of_val av) Itv.bot.
Proof.
intros z [[[i ls] ab] ps] Hv.
apply (@Itv.non_bot z i).
exact (val_g_z_inv Hv).
Qed.

Lemma val_g_z_val_non_bot :
  forall z av (Hv : Val_g (DomCon.val_of_z z) av),
    ~ Val.eq av Val.bot.
Proof.
intros z [[[i ls] ab] ps] Hv Heq.
destruct Heq as [[[Hi _] _] _].
eapply val_g_z_itv_non_bot; [by apply Hv|by apply Hi].
Qed.

Lemma gamma_of_ints :
  forall z lb ub (Hz : lb <= z <= ub), Itv.gamma z (Itv.of_ints lb ub).
Proof.
intros. unfold Itv.of_ints.
destruct (Z_le_dec lb ub); [constructor; constructor; lia|lia].
Qed.

Lemma gamma_join_left :
  forall z x y (Hx : Itv.gamma z x), Itv.gamma z (Itv.join x y).
Proof. i. eapply Itv.gamma_monotone; [by apply Hx|by apply Itv.join_left]. Qed.

Lemma gamma_join_right :
  forall z x y (Hy : Itv.gamma z y), Itv.gamma z (Itv.join x y).
Proof. i. eapply Itv.gamma_monotone; [by apply Hy|by apply Itv.join_right]. Qed.

Lemma gamma_false_itv_eq_zero :
  forall z i (Hz : Itv.gamma z i) (Hi : Itv.eq i Itv.false_itv), z = 0.
Proof.
i. assert (Itv.gamma z Itv.false_itv) as Hz0.
{ eapply Itv.gamma_mor; [reflexivity|by apply Hi|by apply Hz]. }
inversion Hz0; subst. inversion Hle1; inversion Hle2; lia.
Qed.

Lemma cor_eval_const :
  forall c v (Hc : SemCon.Eval_const c v), Val_g v (SemEval.eval_const c).
Proof.
destruct 1; unfold SemEval.eval_const; apply Val_g_z.
- by apply Itv.cor_itv_top.
- by apply Itv.cor_of_int.
- by apply Itv.cor_of_int.
- by apply gamma_of_ints.
- by apply Itv.cor_itv_top.
Qed.

Lemma cor_eval_uop :
  forall op v v' abs_v (Hu : SemCon.Eval_uop op v v') (Habs : Val_g v abs_v),
    Val_g v' (SemEval.eval_uop op abs_v).
Proof.
i. unfold SemEval.eval_uop.
destruct (Val.eq_dec abs_v Val.bot) as [Hbot|Hnbot].
{ inversion Hu; subst; exfalso; eapply val_g_z_val_non_bot; eauto. }
inversion Hu; subst; apply Val_g_z.
- replace (- z)%Z with (0 - z)%Z by lia.
  apply Itv.cor_minus; [by apply Itv.cor_of_int|by eapply val_g_z_gamma].
- apply Itv.unknown_unary_prop.
  eapply val_g_z_itv_non_bot. by apply Habs.
- eapply (@Itv.not_itv_prop1 z); [by auto|exact (val_g_z_gamma Habs)].
- apply Itv.not_itv_prop2. exact (val_g_z_gamma Habs).
Qed.

Lemma cor_and1 :
  forall z1 z2 i1 i2
     (Hz1n : z1 <> 0) (Hz2n : z2 <> 0)
     (Hz1 : Itv.gamma z1 i1) (Hz2 : Itv.gamma z2 i2),
    Itv.gamma 1 (Itv.and_itv i1 i2).
Proof.
i. unfold Itv.and_itv.
destruct (Itv.eq_dec i1 Itv.Bot ||| Itv.eq_dec i2 Itv.Bot) as [[Hbot|Hbot]|_].
{ eapply Itv.non_bot in Hz1; by eauto. }
{ eapply Itv.non_bot in Hz2; by eauto. }
destruct (Itv.eq_dec i1 Itv.false_itv ||| Itv.eq_dec i2 Itv.false_itv)
  as [[Hfalse|Hfalse]|_].
- assert (z1 = 0) by (eapply gamma_false_itv_eq_zero; eauto). by auto.
- assert (z2 = 0) by (eapply gamma_false_itv_eq_zero; eauto). by auto.
- destruct (~~ Itv.le_dec Itv.false_itv i1 &&&
            ~~ Itv.le_dec Itv.false_itv i2)
  ; [by apply Itv.true_itv_prop|by apply Itv.unknown_bool_prop1].
Qed.

Lemma cor_and0_l :
  forall z i1 i2 (Hz1 : Itv.gamma 0 i1) (Hz2 : Itv.gamma z i2),
    Itv.gamma 0 (Itv.and_itv i1 i2).
Proof.
i. unfold Itv.and_itv.
destruct (Itv.eq_dec i1 Itv.Bot ||| Itv.eq_dec i2 Itv.Bot) as [[Hbot|Hbot]|_].
{ eapply Itv.non_bot in Hz1; by eauto. }
{ eapply Itv.non_bot in Hz2; by eauto. }
destruct (Itv.eq_dec i1 Itv.false_itv ||| Itv.eq_dec i2 Itv.false_itv)
; [by apply Itv.false_itv_prop|].
destruct (~~ Itv.le_dec Itv.false_itv i1 &&&
          ~~ Itv.le_dec Itv.false_itv i2) as [[Hzero _]|_].
{ elim Hzero. by apply Itv.false_itv1. }
by apply Itv.unknown_bool_prop0.
Qed.

Lemma cor_and0_r :
  forall z i1 i2 (Hz1 : Itv.gamma z i1) (Hz2 : Itv.gamma 0 i2),
    Itv.gamma 0 (Itv.and_itv i1 i2).
Proof.
i. unfold Itv.and_itv.
destruct (Itv.eq_dec i1 Itv.Bot ||| Itv.eq_dec i2 Itv.Bot) as [[Hbot|Hbot]|_].
{ eapply Itv.non_bot in Hz1; by eauto. }
{ eapply Itv.non_bot in Hz2; by eauto. }
destruct (Itv.eq_dec i1 Itv.false_itv ||| Itv.eq_dec i2 Itv.false_itv)
; [by apply Itv.false_itv_prop|].
destruct (~~ Itv.le_dec Itv.false_itv i1 &&&
          ~~ Itv.le_dec Itv.false_itv i2) as [[_ Hzero]|_].
{ elim Hzero. by apply Itv.false_itv1. }
by apply Itv.unknown_bool_prop0.
Qed.

Lemma cor_or1_l :
  forall z1 z2 i1 i2
     (Hz1n : z1 <> 0)
     (Hz1 : Itv.gamma z1 i1) (Hz2 : Itv.gamma z2 i2),
    Itv.gamma 1 (Itv.or_itv i1 i2).
Proof.
i. unfold Itv.or_itv.
destruct (Itv.eq_dec i1 Itv.Bot ||| Itv.eq_dec i2 Itv.Bot) as [[Hbot|Hbot]|_].
{ eapply Itv.non_bot in Hz1; by eauto. }
{ eapply Itv.non_bot in Hz2; by eauto. }
destruct (Itv.eq_dec i1 Itv.false_itv &&& Itv.eq_dec i2 Itv.false_itv)
  as [[Hfalse _]|_].
{
  assert (z1 = 0) by (eapply gamma_false_itv_eq_zero; eauto). by auto. }
destruct (~~ Itv.le_dec Itv.false_itv i1 |||
          ~~ Itv.le_dec Itv.false_itv i2)
; [by apply Itv.true_itv_prop|by apply Itv.unknown_bool_prop1].
Qed.

Lemma cor_or1_r :
  forall z1 z2 i1 i2
     (Hz2n : z2 <> 0)
     (Hz1 : Itv.gamma z1 i1) (Hz2 : Itv.gamma z2 i2),
    Itv.gamma 1 (Itv.or_itv i1 i2).
Proof.
i. unfold Itv.or_itv.
destruct (Itv.eq_dec i1 Itv.Bot ||| Itv.eq_dec i2 Itv.Bot) as [[Hbot|Hbot]|_].
{ eapply Itv.non_bot in Hz1; by eauto. }
{ eapply Itv.non_bot in Hz2; by eauto. }
destruct (Itv.eq_dec i1 Itv.false_itv &&& Itv.eq_dec i2 Itv.false_itv)
  as [[_ Hfalse]|_].
{
  assert (z2 = 0) by (eapply gamma_false_itv_eq_zero; eauto). by auto. }
destruct (~~ Itv.le_dec Itv.false_itv i1 |||
          ~~ Itv.le_dec Itv.false_itv i2)
; [by apply Itv.true_itv_prop|by apply Itv.unknown_bool_prop1].
Qed.

Lemma cor_or0 :
  forall i1 i2 (Hz1 : Itv.gamma 0 i1) (Hz2 : Itv.gamma 0 i2),
    Itv.gamma 0 (Itv.or_itv i1 i2).
Proof.
i. unfold Itv.or_itv.
destruct (Itv.eq_dec i1 Itv.Bot ||| Itv.eq_dec i2 Itv.Bot) as [[Hbot|Hbot]|_].
{ eapply Itv.non_bot in Hz1; by eauto. }
{ eapply Itv.non_bot in Hz2; by eauto. }
destruct (Itv.eq_dec i1 Itv.false_itv &&& Itv.eq_dec i2 Itv.false_itv)
; [by apply Itv.false_itv_prop|].
destruct (~~ Itv.le_dec Itv.false_itv i1 |||
          ~~ Itv.le_dec Itv.false_itv i2) as [[Hzero|Hzero]|_].
{ elim Hzero. by apply Itv.false_itv1. }
{ elim Hzero. by apply Itv.false_itv1. }
by apply Itv.unknown_bool_prop0.
Qed.

Lemma cor_plus_offset :
  forall step alloc o sz st z idx ab
     (Hz : Itv.gamma z idx)
     (Hab : ArrayBlk_g (step, alloc, (o, sz, st)) ab),
    ArrayBlk_g (step, alloc, ((o + z)%Z, sz, st))
               (ArrayBlk.plus_offset ab idx).
Proof.
intros. inversion Hab; subst.
unfold ArrayBlk.plus_offset.
destruct (Itv.eq_dec idx Itv.bot) as [Hidx|Hidx].
{ exfalso. eapply Itv.non_bot; [by apply Hz|by apply Hidx]. }
econstructor.
- erewrite ArrayBlk.map_1; [| |by apply Hfind].
  + unfold ArrInfo.plus_offset, ArrInfo.make.
    destruct (Itv.eq_dec Itv.bot io) as [Hio|Hio].
    * exfalso. eapply Itv.non_bot; [by apply Ho|by apply Itv.eq_sym].
    * reflexivity.
  + unfold ArrInfo.plus_offset, ArrInfo.bot; simpl.
    destruct (Itv.eq_dec Itv.bot Itv.bot) as [_|Hneq]
    ; [reflexivity|elim Hneq; by apply Itv.eq_refl].
- by apply Itv.cor_plus.
- by apply Hsz.
- by apply Hst.
Qed.

Lemma cor_minus_offset :
  forall step alloc o sz st z idx ab
     (Hz : Itv.gamma z idx)
     (Hab : ArrayBlk_g (step, alloc, (o, sz, st)) ab),
    ArrayBlk_g (step, alloc, ((o - z)%Z, sz, st))
               (ArrayBlk.minus_offset ab idx).
Proof.
intros. inversion Hab; subst.
unfold ArrayBlk.minus_offset.
destruct (Itv.eq_dec idx Itv.bot) as [Hidx|Hidx].
{ exfalso. eapply Itv.non_bot; [by apply Hz|by apply Hidx]. }
econstructor.
- erewrite ArrayBlk.map_1; [| |by apply Hfind].
  + unfold ArrInfo.minus_offset, ArrInfo.make.
    destruct (Itv.eq_dec Itv.bot io) as [Hio|Hio].
    * exfalso. eapply Itv.non_bot; [by apply Ho|by apply Itv.eq_sym].
    * reflexivity.
  + unfold ArrInfo.minus_offset, ArrInfo.bot; simpl.
    destruct (Itv.eq_dec Itv.bot Itv.bot) as [_|Hneq]
    ; [reflexivity|elim Hneq; by apply Itv.eq_refl].
- by apply Itv.cor_minus.
- by apply Hsz.
- by apply Hst.
Qed.

Lemma cor_plus_pi :
  forall step alloc o sz st z idx v
     (Hz : Itv.gamma z idx)
     (Hv : Val_g
             (DomCon.val_of_loc
                (DomCon.loc_of_alloc
                   step alloc (o, sz, st) DomCon.Fields.nil))
             v),
    Val_g
      (DomCon.val_of_loc
         (DomCon.loc_of_alloc step alloc ((o + z)%Z, sz, st) DomCon.Fields.nil))
      (Val.join
         (SemEval.array_loc_of_val v)
         (val_of_array (ArrayBlk.plus_offset (array_of_val v) idx))).
Proof.
i; inversion_clear Hv; subst.
- eapply val_g_monotone; [apply Val_g_loc|by apply Val.join_left].
  unfold DomCon.loc_of_alloc, Loc_g, VarRegion_g in *.
  apply PowLoc.filter1; [by apply SemEval.is_array_loc_mor|by apply Hl|by auto].
- eapply val_g_monotone; [apply Val_g_ab|by apply Val.join_right].
  by eapply cor_plus_offset.
Qed.

Lemma cor_minus_pi :
  forall step alloc o sz st z idx v
     (Hz : Itv.gamma z idx)
     (Hv : Val_g
             (DomCon.val_of_loc
                (DomCon.loc_of_alloc
                   step alloc (o, sz, st) DomCon.Fields.nil))
             v),
    Val_g
      (DomCon.val_of_loc
         (DomCon.loc_of_alloc step alloc ((o - z)%Z, sz, st) DomCon.Fields.nil))
      (Val.join
         (SemEval.array_loc_of_val v)
         (val_of_array (ArrayBlk.minus_offset (array_of_val v) idx))).
Proof.
i; inversion_clear Hv; subst.
- eapply val_g_monotone; [apply Val_g_loc|by apply Val.join_left].
  unfold DomCon.loc_of_alloc, Loc_g, VarRegion_g in *.
  apply PowLoc.filter1; [by apply SemEval.is_array_loc_mor|by apply Hl|by auto].
- eapply val_g_monotone; [apply Val_g_ab|by apply Val.join_right].
  by eapply cor_minus_offset.
Qed.

Lemma cor_eval_bop :
  forall op v1 v2 v' abs_v1 abs_v2 (Hu : SemCon.Eval_bop op v1 v2 v')
     (Habs1 : Val_g v1 abs_v1) (Habs2 : Val_g v2 abs_v2),
    Val_g v' (SemEval.eval_bop op abs_v1 abs_v2).
Proof.
inversion_clear 1; subst; i; unfold SemEval.eval_bop.
{ inversion Habs1; subst; inversion Habs2; subst.
  apply Val_g_z. by apply Itv.cor_plus. }
{ inversion Habs2; subst. by eapply cor_plus_pi. }
{ inversion Habs2; subst. by eapply cor_plus_pi. }
{ inversion Habs1; subst; inversion Habs2; subst.
  apply Val_g_z. by apply Itv.cor_minus. }
{ inversion Habs2; subst. by eapply cor_minus_pi. }
{ inversion Habs1; subst; inversion Habs2; subst.
  apply Val_g_z. by apply Itv.times_prop. }
{ inversion Habs1; subst; inversion Habs2; subst.
  apply Val_g_z. by apply Itv.divide_prop. }
{ apply Val_g_z. apply Itv.unknown_binary_prop.
  - eapply val_g_z_itv_non_bot. by apply Habs1.
  - eapply val_g_z_itv_non_bot. by apply Habs2. }
{ apply Val_g_z. apply Itv.unknown_binary_prop.
  - eapply val_g_z_itv_non_bot. by apply Habs1.
  - eapply val_g_z_itv_non_bot. by apply Habs2. }
{ apply Val_g_z. apply Itv.unknown_binary_prop.
  - eapply val_g_z_itv_non_bot. by apply Habs1.
  - eapply val_g_z_itv_non_bot. by apply Habs2. }
{ inversion Habs1; subst; inversion Habs2; subst.
  apply Val_g_z. eapply Itv.cor_lt1; eauto. }
{ inversion Habs1; subst; inversion Habs2; subst.
  apply Val_g_z. eapply Itv.cor_lt0; eauto. }
{ inversion Habs1; subst; inversion Habs2; subst.
  apply Val_g_z. unfold Itv.gt_itv.
  eapply (@Itv.cor_lt1 z2 z1); [lia|exact (val_g_z_gamma Habs2)|exact (val_g_z_gamma Habs1)]. }
{ inversion Habs1; subst; inversion Habs2; subst.
  apply Val_g_z. unfold Itv.gt_itv.
  eapply (@Itv.cor_lt0 z2 z1); [intro H; apply Hle; lia|exact (val_g_z_gamma Habs2)|exact (val_g_z_gamma Habs1)]. }
{ inversion Habs1; subst; inversion Habs2; subst.
  apply Val_g_z. eapply Itv.cor_le1; eauto. }
{ inversion Habs1; subst; inversion Habs2; subst.
  apply Val_g_z. eapply Itv.cor_le0; eauto. }
{ inversion Habs1; subst; inversion Habs2; subst.
  apply Val_g_z. unfold Itv.ge_itv.
  eapply (@Itv.cor_le1 z2 z1); [lia|exact (val_g_z_gamma Habs2)|exact (val_g_z_gamma Habs1)]. }
{ inversion Habs1; subst; inversion Habs2; subst.
  apply Val_g_z. unfold Itv.ge_itv.
  eapply (@Itv.cor_le0 z2 z1); [intro H; apply Hlt; lia|exact (val_g_z_gamma Habs2)|exact (val_g_z_gamma Habs1)]. }
{ inversion Habs1; subst; inversion Habs2; subst.
  apply Val_g_z. subst. eapply Itv.cor_eq1; eauto. }
{ inversion Habs1; subst; inversion Habs2; subst.
  apply Val_g_z. eapply Itv.cor_eq0; eauto. }
{ inversion Habs1; subst; inversion Habs2; subst.
  apply Val_g_z. eapply Itv.cor_ne1; eauto. }
{ inversion Habs1; subst; inversion Habs2; subst.
  apply Val_g_z. subst. eapply Itv.cor_ne0; eauto. }
{ apply Val_g_z. apply Itv.unknown_binary_prop.
  - eapply val_g_z_itv_non_bot. by apply Habs1.
  - eapply val_g_z_itv_non_bot. by apply Habs2. }
{ apply Val_g_z. apply Itv.unknown_binary_prop.
  - eapply val_g_z_itv_non_bot. by apply Habs1.
  - eapply val_g_z_itv_non_bot. by apply Habs2. }
{ apply Val_g_z. apply Itv.unknown_binary_prop.
  - eapply val_g_z_itv_non_bot. by apply Habs1.
  - eapply val_g_z_itv_non_bot. by apply Habs2. }
{ apply Val_g_z. destruct Hz as [Hz1n Hz2n].
  eapply cor_and1; [by apply Hz1n|by apply Hz2n
                   |exact (val_g_z_gamma Habs1)|exact (val_g_z_gamma Habs2)]. }
{ apply Val_g_z.
  eapply cor_and0_l; [exact (val_g_z_gamma Habs1)|exact (val_g_z_gamma Habs2)]. }
{ apply Val_g_z.
  eapply cor_and0_r; [exact (val_g_z_gamma Habs1)|exact (val_g_z_gamma Habs2)]. }
{ apply Val_g_z.
  eapply cor_or1_l; [by apply Hz|exact (val_g_z_gamma Habs1)|exact (val_g_z_gamma Habs2)]. }
{ apply Val_g_z.
  eapply cor_or1_r; [by apply Hz|exact (val_g_z_gamma Habs1)|exact (val_g_z_gamma Habs2)]. }
{ apply Val_g_z. apply cor_or0; [exact (val_g_z_gamma Habs1)|exact (val_g_z_gamma Habs2)]. }
Qed.

Local Close Scope sumbool.

Lemma arrinfo_make_not_bot :
  forall o sz st io is it
     (Ho : Itv.gamma o io) (Hsz : Itv.gamma sz is) (Hst : Itv.gamma st it),
    ~ ArrInfo.eq ArrInfo.bot (ArrInfo.make io is it).
Proof.
intros o sz st io is it Ho Hsz Hst Heq.
unfold ArrInfo.eq, ArrInfo.bot, ArrInfo.make in Heq; simpl in Heq.
destruct Heq as [[Hio _] _].
eapply (@Itv.non_bot o io); [by apply Ho|by apply Itv.eq_sym].
Qed.

Lemma cor_cast :
  forall step alloc o o' sz sz' st st' ab
         (Ho' : o' = (c_div (o * st) st')%Z)
         (Hsz' : sz' = (c_div (sz * st) st')%Z)
         (Hab : ArrayBlk_g (step, alloc, (o, sz, st)) ab),
    ArrayBlk_g (step, alloc, (o', sz', st')) (ArrayBlk.cast_array_int st' ab).
Proof.
intros. inversion Hab; subst.
econstructor.
- unfold ArrayBlk.cast_array_int, ArrayBlk.cast_array.
  erewrite ArrayBlk.map_1; [| |by apply Hfind].
  + unfold ArrInfo.make.
    destruct (Itv.eq_dec Itv.bot it) as [Hit|Hit].
    * exfalso. eapply Itv.non_bot; [by apply Hst|by apply Itv.eq_sym].
    * reflexivity.
  + unfold ArrInfo.bot. simpl.
    destruct (Itv.eq_dec Itv.bot Itv.bot) as [_|Hneq]
    ; [reflexivity|elim Hneq; by apply Itv.eq_refl].
- apply Itv.divide_prop.
  + by apply Itv.times_prop.
  + by apply Itv.cor_of_int.
- apply Itv.divide_prop.
  + by apply Itv.times_prop.
  + by apply Itv.cor_of_int.
- by apply Itv.cor_of_int.
Qed.

Lemma cor_pow_loc_of_array :
  forall r ab (Hr : ArrayBlk_g r ab),
    PowLoc.mem (Loc_g (DomCon.VarRegion.Inr r, DomCon.Fields.nil))
               (ArrayBlk.pow_loc_of_array ab) = true.
Proof.
inversion 1; subst; s.
unfold ArrayBlk.pow_loc_of_array.
eapply ArrayBlk.foldi_1 with (teq:=PowLoc.eq) (k:=Allocsite_g a).
- constructor
  ; [ intros ?; by apply PowLoc.eq_refl
    | intros ? ? ?; by apply PowLoc.eq_trans
    | intros ? ?; by apply PowLoc.eq_sym ].
- intros ls1 ls2 Hls; split; intro Hmem.
  + rewrite PowLoc.mem_mor
    ; [by apply Hmem|by apply Loc.eq_refl|by apply PowLoc.eq_sym].
  + rewrite PowLoc.mem_mor; [by apply Hmem|by apply Loc.eq_refl|by auto].
- rewrite Hfind. by apply ArrInfo.eq_refl.
- destruct (ArrInfo.eq_dec ArrInfo.bot (ArrInfo.make io is it)).
  + exfalso. eapply (@arrinfo_make_not_bot o sz st io is it); eauto.
  + i; apply DomBasic.PowLoc.mem_add_1; by apply Loc.eq_refl.
- i; destruct (ArrInfo.eq_dec ArrInfo.bot v)
  ; [by apply PowLoc.eq_refl|by elim f].
- i; destruct (ArrInfo.eq_dec ArrInfo.bot v); [by auto|].
  by apply PowLoc.mem_add_3.
- i; destruct (ArrInfo.eq_dec ArrInfo.bot v1).
  + destruct (ArrInfo.eq_dec ArrInfo.bot v2)
    ; [|elim f; eapply ArrInfo.eq_trans; [by apply e|by auto]].
    by auto.
  + destruct (ArrInfo.eq_dec ArrInfo.bot v2)
    ; [ elim f; eapply ArrInfo.eq_trans; [by apply e|by apply ArrInfo.eq_sym]
      | rewrite <- Hf ].
    apply PowLoc.mem_mor; [by auto|].
    apply PowLoc.add_mor; [|by apply PowLoc.eq_refl].
    apply DomBasic.loc_of_allocsite_mor; by apply Allocsite.eq_sym.
Qed.

Lemma cor_deref_of_val :
  forall l v (Habs : Val_g (DomCon.val_of_loc l) v),
    PowLoc.mem (Loc_g l) (SemEval.deref_of_val v) = true.
Proof.
inversion 1; subst.
- unfold SemEval.deref_of_val.
  eapply PowLoc.le_mem_true; [by apply PowLoc.join_left|by apply Hl].
- unfold SemEval.deref_of_val.
  eapply PowLoc.le_mem_true; [by apply PowLoc.join_right|].
  apply cor_pow_loc_of_array. by apply Hl.
Qed.

Lemma cor_fields_app :
  forall fs n f,
    Fields.eq' n (Fields_g (SemCon.fields_app1 fs f))
               (Fields.app (Fields_g fs) f).
Proof.
induction fs.
- i; s; by apply Fields.eq'_refl.
- i; s. destruct n; [by constructor|].
  constructor; [by auto|by apply IHfs].
Qed.

Lemma cor_append_field :
  forall va fs f v (Hl : Val_g (DomCon.val_of_loc (va, fs)) v),
    PowLoc.mem (Loc_g (va, SemCon.fields_app1 fs f))
               (PowLoc.join
                  (DomBasic.pow_loc_append_field (DomAbs.pow_loc_of_val v) f)
                  (ArrayBlk.pow_loc_of_struct_w_field (DomAbs.array_of_val v) f)) =
    true.
Proof.
inversion 1; subst; clear Hl.
- eapply PowLoc.mem_monotone1
  ; [by apply Loc.eq_refl|by apply PowLoc.join_left|].
  unfold DomBasic.pow_loc_append_field.
  remember (fun l : Loc.t' => append_field l f) as append_f.
  assert
    (Loc.eq (Loc_g (va, SemCon.fields_app1 fs f)) (append_f (Loc_g (va, fs))))
  as Hl.
  + rewrite Heqappend_f. unfold append_field, Loc_g. constructor; s.
    split; [by apply VarAllocsite.eq_refl|by apply cor_fields_app].
  + rewrite Hl. apply SMLocLoc.map_1; [|by apply Hl0].
    intros l1 l2 Hl'. subst. by apply DomBasic.append_field_mor.
- eapply PowLoc.mem_monotone1
  ; [by apply Loc.eq_refl|by apply PowLoc.join_right|].
  unfold ArrayBlk.pow_loc_of_struct_w_field.
  inversion Hl0; subst; clear Hl0.
  apply ArrayBlk.foldi_1
  with (teq:=PowLoc.eq) (k:=Allocsite_g a) (v:=ArrInfo.make io is it).
  + constructor
    ; [ intros ?; by apply PowLoc.eq_refl
      | intros ? ? ?; by apply PowLoc.eq_trans
      | intros ? ?; by apply PowLoc.eq_sym ].
  + intros l1 l2 Hl; split; intro Hmem.
    * rewrite DomBasic.PowLoc.mem_mor
      ; [by apply Hmem|by apply Loc.eq_refl|by apply PowLoc.eq_sym].
    * rewrite DomBasic.PowLoc.mem_mor
      ; [by apply Hmem|by apply Loc.eq_refl|by auto].
  + unfold DomAbs.array_of_val.
    rewrite <- Hfind; by apply ArrInfo.eq_refl.
  + i; dest_if_dec.
    * exfalso. eapply (@arrinfo_make_not_bot o sz st io is it); eauto.
      by apply ArrInfo.eq_sym.
    * apply PowLoc.mem_add_1.
      constructor; split; [by apply VarAllocsite.eq_refl|by apply cor_fields_app].
  + i. dest_if_dec. elim f0; by apply ArrInfo.eq_sym.
  + i; dest_if_dec. by apply PowLoc.mem_add_3.
  + i. destruct (ArrInfo.eq_dec v1 ArrInfo.bot).
    * destruct (ArrInfo.eq_dec v2 ArrInfo.bot)
      ; [| elim f0; eapply ArrInfo.eq_trans
           ; [apply ArrInfo.eq_sym; by apply Hv|by auto] ].
      by auto.
    * destruct (ArrInfo.eq_dec v2 ArrInfo.bot)
      ; [elim f0; eapply ArrInfo.eq_trans; [by apply Hv|by auto]|].
      rewrite <- Hf. apply PowLoc.mem_mor; [by apply Loc.eq_refl|].
      apply PowLoc.add_mor; [|by apply PowLoc.eq_refl].
      apply DomBasic.append_field_mor; [|by apply Field.eq_refl].
      apply DomBasic.loc_of_allocsite_mor; by apply Allocsite.eq_sym.
Qed.

Lemma cor_plus_offset_val :
  forall step alloc o idx sz st abs_v idx_itv
     (Hidx : Itv.gamma idx idx_itv)
     (Habs : Val_g
               (DomCon.val_of_loc
                  (DomCon.loc_of_alloc
                     step alloc (o, sz, st) DomCon.Fields.nil))
               abs_v),
    Val_g
      (DomCon.val_of_loc
         (DomCon.loc_of_alloc
            step alloc ((o + idx)%Z, sz, st) DomCon.Fields.nil))
      (modify_array abs_v (ArrayBlk.plus_offset (array_of_val abs_v) idx_itv)).
Proof.
i. inversion Habs; subst.
+ apply Val_g_loc. by apply Hl.
+ unfold modify_array, DomAbs.array_of_val, DomAbs.pow_loc_of_val, DomAbs.itv_of_val,
          DomAbs.pow_proc_of_val.
  apply Val_g_ab. by eapply cor_plus_offset.
Qed.

Local Open Scope sumbool.

Lemma cor_eval :
  forall step cn e cid callee m d abs_m
         (Hm : Mem_g (cid, callee, m, d) abs_m)
         v (Heval : SemCon.Eval_exp step cn cid m e v),
    Val_g v (eval Strong cn e abs_m)

with cor_eval_lv :
  forall step cn lv cid callee m d abs_m
    (Hm : Mem_g (cid, callee, m, d) abs_m)
    l (Heval : SemCon.Eval_lv step cn cid m lv l),
    PowLoc.mem (Loc_g l)
               (eval_lv Strong cn lv abs_m)
    = true

with cor_resolve_offset :
  forall cn step cid callee m d o l l' abs_m
         (Hm : Mem_g (cid, callee, m, d) abs_m)
         (Hres : SemCon.Resolve_offset step cn cid m l o l')
         v (Hl : Val_g (DomCon.val_of_loc l) v),
    PowLoc.mem (Loc_g l')
               (resolve_offset Strong cn v o abs_m)
    = true.
Proof.
induction 2.
{ s. apply cor_eval_const. by apply Hc. }
{ s. eapply cor_mem_lookup; [|by apply Hm0|by apply Hm].
  eapply cor_eval_lv; [by apply Hm|by apply Hl].
}
{ s. apply Val_g_z. by apply Itv.cor_of_int. }
{ s. apply Val_g_z. by apply Itv.cor_of_int. }
{ s. apply Val_g_z. unfold string_lengthZ. by apply Itv.cor_of_int. }
{ s. apply Val_g_z. by apply Itv.cor_of_int. }
{ s. apply Val_g_z. by apply Itv.cor_itv_top. }
{ s. eapply cor_eval_uop; [by apply Hu|by apply IHHeval]. }
{ s. eapply cor_eval_bop; [by apply Hb|by apply IHHeval1|by apply IHHeval2]. }
{ s. unfold MId.bind, MId.ret.
  destruct (Itv.eq_dec (itv_of_val (eval Strong cn e1 abs_m)) Itv.bot) as [Hbot|Hbot].
  - exfalso. eapply val_g_z_itv_non_bot; [by apply IHHeval1|by apply Hbot].
  - destruct (Itv.eq_dec (itv_of_val (eval Strong cn e1 abs_m)) Itv.zero) as [Hzero|Hzero].
    + assert (z = 0) as Hz0.
      { eapply gamma_false_itv_eq_zero; [by apply val_g_z_gamma, IHHeval1|by apply Hzero]. }
      by auto.
    + destruct (~~ Itv.le_dec Itv.zero (itv_of_val (eval Strong cn e1 abs_m))) as [_|_].
      * by apply IHHeval2.
      * eapply val_g_monotone; [by apply IHHeval2|by apply Val.join_left].
}
{ s. unfold MId.bind, MId.ret.
  destruct (Itv.eq_dec (itv_of_val (eval Strong cn e1 abs_m)) Itv.bot) as [Hbot|Hbot].
  - exfalso. eapply val_g_z_itv_non_bot; [by apply IHHeval1|by apply Hbot].
  - destruct (Itv.eq_dec (itv_of_val (eval Strong cn e1 abs_m)) Itv.zero) as [Hzero|Hzero].
    + by apply IHHeval2.
    + destruct (~~ Itv.le_dec Itv.zero (itv_of_val (eval Strong cn e1 abs_m))) as [Hnle|_].
      * elim Hnle. by apply Itv.false_itv1, val_g_z_gamma.
      * eapply val_g_monotone; [by apply IHHeval2|by apply Val.join_right].
}
{ s. unfold MId.bind, MId.ret.
  rewrite Hl in IHHeval. inversion_clear IHHeval.
  - apply Val_g_loc. rewrite Hl'. simpl in *. by apply Hl0.
  - rewrite Hl'. unfold modify_array, DomAbs.array_of_val.
    apply Val_g_ab. eapply cor_cast; [by apply Ho'|by apply Hsz'|by apply Hl0].
}
{ s. constructor. eapply cor_eval_lv; [by apply Hm|by apply Hl]. }
{ s. constructor. eapply cor_eval_lv; [by apply Hm|by apply Hl]. }

induction 2.
{ s. eapply cor_resolve_offset; [by apply Hm|by apply Ho|].
  constructor. apply PowLoc.singleton_1. by apply Loc.eq_refl. }
{ s. eapply cor_resolve_offset; [by apply Hm|by apply Ho|].
  constructor. apply PowLoc.singleton_1. by apply Loc.eq_refl. }
{ s. eapply cor_resolve_offset; [by apply Hm|by apply Ho|].
  eapply cor_eval; [by apply Hm|by apply Hv]. }

induction 2; i.
{ s. apply cor_deref_of_val. by apply Hl. }
{ s. eapply IHHres. constructor. eapply cor_append_field. by apply Hl. }
{ s. unfold MId.bind, MId.ret.
  eapply IHHres.
  rewrite Hl'. eapply cor_plus_offset_val.
  - eapply val_g_z_gamma. eapply cor_eval; [by apply Hm|by apply Hv].
  - eapply cor_mem_lookup.
    + apply cor_deref_of_val; by apply Hl0.
    + rewrite <- Hl; by apply Hm0.
    + by apply Hm.
}
Qed.

Lemma gamma_zero_pos :
  forall z (Hz : 0 <= z), Itv.gamma z Itv.zero_pos.
Proof.
intros. unfold Itv.zero_pos, Itv.of_lb.
constructor; constructor; lia.
Qed.

Lemma gamma_singleton_le :
  forall z i (Hz : Itv.gamma z i), Itv.le (Itv.of_int z) i.
Proof.
intros. inversion Hz; subst. unfold Itv.of_int. constructor; by auto.
Qed.

Lemma gamma_meet :
  forall z i1 i2 (H1 : Itv.gamma z i1) (H2 : Itv.gamma z i2),
    Itv.gamma z (Itv.meet i1 i2).
Proof.
i. eapply Itv.gamma_monotone; [by apply Itv.cor_of_int|].
apply Itv.meet_glb; by apply gamma_singleton_le.
Qed.

Lemma le_int_minus_one :
  forall x y ub (Hlt : x < y) (Hy : Itv.le' (Itv.Int y) ub),
    Itv.le' (Itv.Int x) (Itv.minus'_one ub).
Proof.
intros. destruct ub; simpl in *; inversion Hy; subst; constructor; lia.
Qed.

Lemma le_plus_one_int :
  forall x y lb (Hlt : y < x) (Hy : Itv.le' lb (Itv.Int y)),
    Itv.le' (Itv.plus'_one lb) (Itv.Int x).
Proof.
intros. destruct lb; simpl in *; inversion Hy; subst; constructor; lia.
Qed.

Lemma gamma_prune_lt :
  forall x y xi yi
     (Hlt : x < y) (Hx : Itv.gamma x xi) (Hy : Itv.gamma y yi),
    Itv.gamma x (SemPrune.itv_prune Syn.Lt xi yi).
Proof.
i. unfold SemPrune.itv_prune.
inversion Hx; subst; inversion Hy; subst.
eapply Itv.gamma_monotone; [by apply Itv.cor_of_int|].
unfold Itv.of_int. apply Itv.le_gen_itv_right.
- by apply Hle1.
- apply Itv.min'3; [by apply Hle2|].
  by eapply (@le_int_minus_one x y ub0).
Qed.

Lemma gamma_prune_gt :
  forall x y xi yi
     (Hgt : x > y) (Hx : Itv.gamma x xi) (Hy : Itv.gamma y yi),
    Itv.gamma x (SemPrune.itv_prune Syn.Gt xi yi).
Proof.
i. unfold SemPrune.itv_prune.
inversion Hx; subst; inversion Hy; subst.
eapply Itv.gamma_monotone; [by apply Itv.cor_of_int|].
unfold Itv.of_int. apply Itv.le_gen_itv_right.
- apply Itv.max'3; [by apply Hle1|].
  eapply (@le_plus_one_int x y lb0); [lia|by apply Hle0].
- by apply Hle2.
Qed.

Lemma gamma_prune_le :
  forall x y xi yi
     (Hle : x <= y) (Hx : Itv.gamma x xi) (Hy : Itv.gamma y yi),
    Itv.gamma x (SemPrune.itv_prune Syn.Le xi yi).
Proof.
i. unfold SemPrune.itv_prune.
inversion Hx; subst; inversion Hy; subst.
eapply Itv.gamma_monotone; [by apply Itv.cor_of_int|].
unfold Itv.of_int. apply Itv.le_gen_itv_right.
- by apply Hle1.
- apply Itv.min'3; [by apply Hle2|].
  eapply Itv.le'_trans; [|by apply Hle3]. constructor; lia.
Qed.

Lemma gamma_prune_ge :
  forall x y xi yi
     (Hge : x >= y) (Hx : Itv.gamma x xi) (Hy : Itv.gamma y yi),
    Itv.gamma x (SemPrune.itv_prune Syn.Ge xi yi).
Proof.
i. unfold SemPrune.itv_prune.
inversion Hx; subst; inversion Hy; subst.
eapply Itv.gamma_monotone; [by apply Itv.cor_of_int|].
unfold Itv.of_int. apply Itv.le_gen_itv_right.
- apply Itv.max'3; [by apply Hle1|].
  eapply Itv.le'_trans; [by apply Hle0|]. constructor; lia.
- by apply Hle2.
Qed.

Lemma gamma_prune_eq :
  forall x xi yi (Hx : Itv.gamma x xi) (Hy : Itv.gamma x yi),
    Itv.gamma x (SemPrune.itv_prune Syn.Eq xi yi).
Proof.
i. unfold SemPrune.itv_prune.
inversion Hx; subst; inversion Hy; subst.
by apply gamma_meet.
Qed.

Lemma itv_prune_sound :
  forall op x y z xi yi
     (Hb : SemCon.Eval_bop op (DomCon.val_of_z x) (DomCon.val_of_z y) (DomCon.val_of_z z))
     (Hnz : z <> 0)
     (Hx : Itv.gamma x xi) (Hy : Itv.gamma y yi),
    Itv.gamma x (SemPrune.itv_prune op xi yi).
Proof.
inversion 1; subst; i.
all: try solve
  [ unfold SemPrune.itv_prune
  ; destruct xi; [destruct yi|]; simpl
  ; try assumption; try inversion Hx; try inversion Hy ].
- by eapply (@gamma_prune_lt x y xi yi).
- by exfalso; apply Hnz.
- by eapply (@gamma_prune_gt x y xi yi).
- by exfalso; apply Hnz.
- by eapply (@gamma_prune_le x y xi yi).
- by exfalso; apply Hnz.
- by eapply (@gamma_prune_ge x y xi yi).
- by exfalso; apply Hnz.
- subst. by apply gamma_prune_eq.
- by exfalso; apply Hnz.
Qed.

Lemma val_g_modify_prune :
  forall op x y z xv yv
     (Hb : SemCon.Eval_bop op (DomCon.val_of_z x) (DomCon.val_of_z y) (DomCon.val_of_z z))
     (Hnz : z <> 0)
     (Hx : Val_g (DomCon.val_of_z x) xv)
     (Hy : Val_g (DomCon.val_of_z y) yv),
    Val_g (DomCon.val_of_z x)
          (modify_itv xv
             (SemPrune.itv_prune op (itv_of_val xv) (itv_of_val yv))).
Proof.
i. unfold modify_itv. apply Val_g_z.
eapply itv_prune_sound; [by apply Hb|by apply Hnz| |].
- by apply val_g_z_gamma.
- by apply val_g_z_gamma.
Qed.

Lemma cor_prune :
  forall g step cn cid callee m d e z abs_m
     (Hmem_g : Mem_g (cid, callee, m, d) abs_m)
     (Heval : SemCon.Eval_exp step cn cid m e (DomCon.val_of_z z))
     (Hnz : z <> 0)
     (Hwf : SemCon.wf_non_rec_mem g m),
    Mem_g (cid, callee, m, d) (RunOnly.SemPrune.prune g Strong cn e abs_m).
Proof.
i. unfold RunOnly.SemPrune.prune.
destruct e; try by apply Hmem_g.
destruct e1; try by apply Hmem_g.
match goal with
| lv : Syn.lval |- _ => destruct lv as [lh ofs lpos]
end.
destruct lh as [x is_global|]; try by apply Hmem_g.
destruct ofs; try by apply Hmem_g.
unfold MId.bind, MId.ret.
inversion Heval; subst.
inversion Hv1; subst.
assert (Hx_abs :
          Val_g v1
                (mem_lookup
                   (PowLoc.singleton (SemEval.eval_var cn x is_global))
                   abs_m)).
{ eapply cor_mem_lookup; [|by apply Hm|by apply Hmem_g].
  destruct is_global; inversion Hl; subst; inversion Ho; subst
  ; apply PowLoc.singleton_1; by apply Loc.eq_refl. }
assert (Hy_abs : Val_g v2 (eval Strong cn e2 abs_m)).
{ eapply cor_eval; [by apply Hmem_g|by apply Hv2]. }
assert
  (Hprune_abs :
     Val_g v1
       (modify_itv
          (mem_lookup (PowLoc.singleton (SemEval.eval_var cn x is_global)) abs_m)
          (SemPrune.itv_prune b
             (itv_of_val
                (mem_lookup
                   (PowLoc.singleton (SemEval.eval_var cn x is_global))
                   abs_m))
             (itv_of_val (eval Strong cn e2 abs_m))))).
{ inversion Hb; subst; try (by exfalso; apply Hnz).
  all: try (eapply val_g_modify_prune
            ; [by econstructor; eauto|by apply Hnz|by apply Hx_abs|by apply Hy_abs]).
}
destruct is_global; inversion Hl; subst; inversion Ho; subst.
- eapply cor_update'
  with (l := DomCon.loc_of_gvar x DomCon.Fields.nil)
       (l' := SemEval.eval_var cn x true)
  ; [ by apply Loc.eq_refl
    | by apply Hprune_abs
    | by apply Hmem_g
    | reflexivity
    | symmetry; by apply DomCon.M.P.F.find_mapsto_iff
    | by apply Hwf ].
- eapply cor_update'
  with (l := DomCon.loc_of_lvar cid (InterNode.get_pid cn) x DomCon.Fields.nil)
       (l' := SemEval.eval_var cn x false)
  ; [ by apply Loc.eq_refl
    | by apply Hprune_abs
    | by apply Hmem_g
    | reflexivity
    | symmetry; by apply DomCon.M.P.F.find_mapsto_iff
    | by apply Hwf ].
Qed.

Lemma cor_eval_alloc' :
  forall step cn sz
         a (Ha : a = DomCon.Allocsite.Inl cn)
         al (Hal : al = DomCon.loc_of_alloc step a (0%Z, sz, 1%Z) DomCon.Fields.nil)
         v (Hv : Val_g (DomCon.val_of_z sz) v),
    Val_g (DomCon.val_of_loc al) (eval_alloc' cn v).
Proof.
i. rewrite Hal, Ha.
eapply val_g_monotone; [|by apply Val.join_left].
unfold DomCon.val_of_loc.
apply Val_g_loc. s.
unfold loc_of_allocsite, allocsite_of_node.
apply PowLoc.singleton_1; by apply Loc.eq_refl.
Qed.

Lemma cor_eval_string_val :
  forall s z (Hz : 0 <= z),
    Val_g (DomCon.val_of_z z) (SemEval.eval_string s).
Proof.
i. unfold SemEval.eval_string. apply Val_g_z. by apply gamma_zero_pos.
Qed.

Lemma cor_eval_string :
  forall g cn s step sz cid callee d m m' abs_m
     base o (Hbase : base = DomCon.loc_of_alloc step (DomCon.Allocsite.Inl cn) (o, sz, 1%Z) DomCon.Fields.nil)
     (Hinit : SemCon.Initial_s g step (DomCon.Allocsite.Inl cn) base s m m')
     (Hmem_g : Mem_g (cid, callee, m, d) abs_m),
    Mem_g (cid, callee, m', d)
          (mem_wupdate Strong
                      (PowLoc.singleton
                         (loc_of_allocsite (allocsite_of_node cn)))
                      (SemEval.eval_string s) abs_m).
Proof.
induction s.
- i; inversion_clear Hinit; subst.
  eapply cor_wupdate; [| |by apply Hmem_g|reflexivity|reflexivity].
  + apply DomBasic.PowLoc.singleton_1; by apply Loc.eq_refl.
  + apply cor_eval_string_val. lia.
- i; inversion Hinit; subst. inversion Hl; subst.
  eapply mem_g_mor; [reflexivity|by apply mem_wupdate_double|].
  eapply IHs; [reflexivity|by apply Htl|].
  eapply cor_wupdate; [| |by apply Hmem_g|reflexivity|reflexivity].
  + apply DomBasic.PowLoc.singleton_1; by apply Loc.eq_refl.
  + unfold SemCon.val_of_ascii. apply cor_eval_string_val.
    apply Zle_0_nat.
Qed.

Lemma cor_eval_string_loc :
  forall step cn sz s
         a (Ha : a = DomCon.Allocsite.Inl cn)
         base (Hbase : base = DomCon.loc_of_alloc step a (0%Z, sz, 1%Z) DomCon.Fields.nil),
    Val_g (DomCon.val_of_loc base)
          (SemEval.eval_string_loc
             s (allocsite_of_node cn)
             (PowLoc.singleton (loc_of_allocsite (allocsite_of_node cn)))).
Proof.
i. unfold DomCon.val_of_loc, SemEval.eval_string_loc, DomAbs.val_of_pow_loc, DomAbs.val_of_array.
eapply val_g_monotone; [|by apply Val.join_left].
apply Val_g_loc.
rewrite Hbase, Ha. unfold allocsite_of_node, loc_of_allocsite. s.
apply PowLoc.singleton_1. by apply Loc.eq_refl.
Qed.

Lemma cor_ret_some :
  forall callee callee' cid cid' m m' retl d abs_m abs_m'
     (Hmem_g : Mem_g (cid, callee, m, (callee', Some retl, cid') :: d) abs_m)
         v v' (Hv : Val_g v v')
         (Habs_m' : abs_m' = mem_wupdate Strong
                                     (SemEval.deref_of_val
                                        (mem_lookup
                                           (PowLoc.singleton
                                              (loc_of_proc callee'))
                                           abs_m))
                                     v' abs_m)
         (Hm' : DomCon.M.add retl v m = m'),
    Mem_g (cid', callee, m', d) abs_m'.
Proof.
i. rewrite Habs_m', <- Hm'.
eapply cor_wupdate
; [|by apply Hv|eapply weaken_mem_g; by apply Hmem_g|reflexivity|reflexivity].
apply cor_deref_of_val.
destruct Hmem_g as [Hm Hs]. unfold Stack_g in Hs.
assert (Hs' : Val_g (DomCon.val_of_loc retl) (Mem.find (SProc_g callee') abs_m))
; [eapply Hs; s; left; reflexivity|].
eapply val_g_monotone; [by apply Hs'|].
apply mem_find_mem_lookup. apply PowLoc.singleton_1. by apply Loc.eq_refl.
Qed.

Lemma cor_update_rets :
  forall cn cid m d step callee callees ret_opt l_opt abs_m abs_m'
         (Hcallee : PowProc.mem callee callees = true)
         (Hret : SemCon.Eval_lv_opt step cn cid m ret_opt l_opt)
         (Habs : Mem_g (step, Some callee, m, d) abs_m)
         (Hupdate :
            update_rets Strong cn callees ret_opt abs_m
            = abs_m'),
    Mem_g (step, Some callee, m, (callee, l_opt, cid) :: d) abs_m'.
Proof. {
i. subst. unfold update_rets, MId.bind, MId.ret. split.
- apply mem_wupdate_diff; [by apply Habs|].
  i. apply SMProcLoc.map_diff.
  unfold Loc_g, DomBasic.loc_of_proc; destruct l; inversion 1.
- unfold RunOnly.mem_wupdate, mem_wupdate, MId.bind, MId.ret.
  unfold weak_add, DomMem.IdMem.mem_weak_add; s.
  apply cor_update2 with
  (m := abs_m)
  (l' := match ret_opt with
         | Some ret_lv =>
           SemEval.eval_lv Strong cn ret_lv abs_m
         | None => DomBasic.PowLoc.bot
         end).
  + by apply Habs.
  + destruct l_opt; inversion Hret; subst; [constructor|by constructor].
    apply cor_eval_lv with
    (step:=step) (cid:=cid) (m:=m) (d:=d) (callee:=Some callee)
    ; [|by apply Hl].
    split; by apply Habs.
  + apply PowLoc.fold_3; [|by apply Mem.le_refl, Mem.eq_refl].
    i. eapply Mem.le_trans; [by apply Hx|].
    intro. destruct (Loc.eq_dec k e).
    * eapply Val.le_trans; [|by apply Val.le_refl, Mem.weak_add_prop].
      eapply Val.le_trans; [|by apply Val.join_right].
      apply Val.le_refl, Mem.find_mor; [by auto|by apply Mem.eq_refl].
    * rewrite Mem.weak_add_diff; [by apply Val.le_refl, Val.eq_refl|by auto].
	  + destruct ret_opt; [|by apply Val.bot_prop].
	    apply PowLoc.fold_1 with (e:=loc_of_proc callee).
	    * apply SMProcLoc.map_1; [by apply DomBasic.loc_of_proc_mor|by auto].
	    * i.
	      eapply Val.le_trans
	      with (y := Val.join (DomAbs.val_of_pow_loc
	                             (SemEval.eval_lv Strong cn l abs_m))
	                             (Mem.find (loc_of_proc callee) x))
	      ; [ by apply Val.join_left
	        | apply Val.le_refl; apply Mem.weak_add_prop; by apply Loc.eq_refl ].
	    * i; s. destruct (Loc.eq_dec (loc_of_proc callee) e').
	      { eapply Val.le_trans
	        with (y := Val.join (DomAbs.val_of_pow_loc
	                               (SemEval.eval_lv Strong cn l abs_m))
	                              (Mem.find e' x))
	        ; [by apply Val.join_left
	          | apply Val.le_refl; apply Mem.weak_add_prop; by auto]. }
      { rewrite Mem.weak_add_diff; by auto. }
    * i. eapply Val.le_trans; [by apply He0|].
      apply Mem.find_mor'; [by apply Loc.eq_refl|].
      apply Mem.weak_add_mor'
      ; [ by auto
        | by apply Val.le_refl, Val.eq_refl
        | by apply Mem.le_refl, Mem.eq_refl ].
} Qed.

Inductive Val_g_list : list DomCon.val_t -> list Val.t -> Prop :=
| Val_g_list_nil : Val_g_list nil nil
| Val_g_list_cons :
    forall v v' vs vs' (Hv : Val_g v v') (Hvs : Val_g_list vs vs'),
      Val_g_list (cons v vs) (cons v' vs').

Lemma cor_eval_list :
  forall step cn cid callee m d m'
     (Hm : Mem_g (cid, callee, m, d) m')
     es vs (Hvs : SemCon.Eval_list step cn cid m es vs)
     vs' (Hvs' : SemEval.eval_list Strong cn es m' = vs'),
    Val_g_list vs vs'.
Proof.
induction 2; i.
- simpl in Hvs'. subst. by constructor.
- simpl in Hvs'. subst. constructor.
  + eapply cor_eval; [by apply Hm|by apply Hv].
  + by apply IHHvs.
Qed.

Lemma bind_arg_monotone :
  forall f x v, Proper (Mem.le ==> Mem.le) (bind_arg Strong f x v).
Proof. unfold bind_arg. i. by apply mem_wupdate_monotone. Qed.

Lemma cor_bind_arg :
  forall step opt_callee d  callee x v v' m m' abs_m abs_m'
     (Hm_g : Mem_g (step, opt_callee, m, d) abs_m)
     (Hv_g : Val_g v v')
     (Hm :
        DomCon.M.add (DomCon.loc_of_lvar step callee x DomCon.Fields.nil) v m
        = m')
     (Habs_m : bind_arg Strong callee x v' abs_m = abs_m'),
    Mem_g (step, opt_callee, m', d) abs_m'.
Proof.
i; subst. unfold bind_arg.
eapply cor_wupdate; [|by apply Hv_g|by apply Hm_g|reflexivity|reflexivity].
by apply PowLoc.singleton_1.
Qed.

Lemma list_fold2_m_monotone A B :
  forall (f: A -> B -> Mem.t -> Mem.t) l vs
     (Hf : forall a b, Proper (Mem.le ==> Mem.le) (f a b)),
    Proper (Mem.le ==> Mem.le) (list_fold2_m f l vs).
Proof.
induction l.
- intros vs m1 m2 Hm. s. destruct vs; by auto.
- intros vs Hf m1 m2 Hm. s. destruct vs; [by auto|].
  apply IHl; [by auto|by apply Hf].
Qed.

Lemma list_fold2_m_ext A B :
  forall (f : A -> B -> Mem.t -> Mem.t) l m m' vs
     (Hm : Mem.le m m') (Hf : forall a b m, Mem.le m (f a b m)),
    Mem.le m (list_fold2_m f l vs m').
Proof.
induction l.
- i; s. destruct vs; by auto.
- i; s. destruct vs; [by auto|].
  unfold MId.bind. apply IHl; [|by auto].
  eapply Mem.le_trans; [by apply Hm|by apply Hf].
Qed.

Lemma bind_args_monotone :
  forall g vs f, Proper (Mem.le ==> Mem.le) (bind_args Strong g vs f).
Proof.
i. intros m1 m2 Hm. unfold bind_args.
destruct (InterCfg.get_args (Global.G.icfg g) f); [|by auto].
apply list_fold2_m_monotone; [by apply bind_arg_monotone|by auto].
Qed.

Lemma bind_args_ext :
  forall g vs e m, Mem.le m (bind_args Strong g vs e m).
Proof.
unfold bind_args. i. destruct (InterCfg.get_args (Global.G.icfg g) e).
- apply list_fold2_m_ext; [by apply Mem.le_refl, Mem.eq_refl|].
  unfold bind_arg. i. by apply mem_wupdate_ext.
- by apply Mem.le_refl, Mem.eq_refl.
Qed.

Lemma cor_bind_args :
  forall g step opt_callee callee callees callee_args vs vs' m m' d
     abs_m abs_m'
     (Hmem_g : Mem_g (step, opt_callee, m, d) abs_m)
     (Hargs_p : Some callee_args = InterCfg.get_args (Global.G.icfg g) callee)
     (Hbind : SemCon.Bind_list step callee callee_args vs m m')
     (Hval_g : Val_g_list vs vs')
     (Hcallee_g : PowProc.mem callee callees = true)
     (Habs_m' : abs_m' = BJProcMem.weak_big_join
                           (bind_args Strong g vs')
                           callees abs_m),
    Mem_g (step, opt_callee, m', d) abs_m'.
Proof.
i; subst.
eapply mem_g_monotone
; [|apply BJProcMem.weak_big_join_1; [by apply Hcallee_g| |]].
- unfold bind_args. rewrite <- Hargs_p.
  generalize vs m m' Hbind vs' Hval_g abs_m Hmem_g Hcallee_g.
  clear vs vs' m m' abs_m Hmem_g Hargs_p Hbind Hval_g Hcallee_g.
  induction 1; i.
  + inversion Hval_g; subst. simpl list_fold2_m. by apply Hmem_g.
  + inversion Hval_g; subst. simpl list_fold2_m. unfold MId.bind. apply IHHbind.
    * by inversion Hval_g.
    * eapply cor_bind_arg
      ; [by apply Hmem_g|by apply Hv|reflexivity|reflexivity].
    * by auto.
- intros f1 f2 Hf. subst. by apply bind_args_monotone.
- unfold MId.le, MId.ret. i. by apply bind_args_ext.
Qed.

Lemma correct_run :
  forall g step cn cmd con_s con_s' abs_m abs_m'
    (Hmem_g : Mem_g con_s abs_m)
    (HCon : SemCon.Run g step cn cmd con_s con_s')
    (HAbs : abs_m' = run_only Strong g cn cmd abs_m),
    Mem_g con_s' abs_m'.
Proof.
destruct 2.
{ simpl run_only; i; unfold MId.bind in HAbs; subst abs_m'; destruct lv, lh, o
  ; try (eapply cor_update with (l:=l) (g:=g)
         ; [ by apply Loc.eq_refl
           | eapply cor_eval; [by apply Hmem_g|by apply Hv]
           | by apply Hmem_g
           | destruct is_global; inversion Hl; subst; inversion Ho; subst
             ; reflexivity
           | by auto
           | by auto ])
  ; try (eapply cor_wupdate with (l:=l)
         ; [ eapply cor_eval_lv; [by apply Hmem_g|by apply Hl]
           | eapply cor_eval; [by apply Hmem_g|by apply Hv]
           | by apply Hmem_g
           | try (destruct is_global; inversion Hl; subst; inversion Ho; subst)
             ; reflexivity
           | by auto ]).
}
{ simpl run_only. i.
eapply cor_wupdate; [| |by apply Hmem_g|by apply HAbs|symmetry; by apply Hm'].
- eapply cor_eval_lv; [by apply Hmem_g|by apply Hl].
- eapply cor_eval_alloc'; [by apply Ha|by apply Hal|].
  eapply cor_eval; [by apply Hmem_g|by apply Hsz].
}
{ simpl run_only. i.
eapply cor_wupdate; [| | |by apply HAbs|symmetry; by apply Hm''].
- eapply cor_eval_lv; [by apply Hmem_g|by apply Hl].
- eapply cor_eval_string_loc; [by apply Ha|by apply Hbase].
- rewrite Ha in *; eapply cor_eval_string
  ; [by apply Hbase|by apply Hinit|by apply Hmem_g].
}
{ simpl run_only. i.
eapply cor_wupdate
; [| |by apply Hmem_g|by apply HAbs|symmetry; by apply Hm'].
- eapply cor_eval_lv; [by apply Hmem_g|by apply Hl].
- unfold DomCon.val_of_proc, DomAbs.val_of_pow_proc.
  apply Val_g_proc. by apply PowProc.singleton_1.
}
{ simpl run_only. i. rewrite HAbs.
  eapply cor_prune; [by apply Hmem_g|by apply Hv|by apply Hprune|by apply Hwf].
}
{ unfold run_only, run, MId.bind, MId.ret. i.
remember (Global.G.is_undef_e f g) as ud; destruct ud; [discriminate|].
rewrite HAbs. clear HAbs Hf_def Hequd.
eapply cor_bind_args
with (callees := powProc_of_val (eval Strong cn f abs_m))
; [|by apply Hargs_p|by apply Hbind| | |reflexivity].
- eapply cor_update_rets; [|by apply Hret|by apply Hmem_g|reflexivity].
  exploit cor_eval; [by apply Hmem_g|by apply Hf|].
  i. inversion x0; subst.
  assert (RunOnly.eval = eval) as eval'; [reflexivity|by rewrite eval', <- H].
- eapply cor_eval_list; [by apply Hmem_g|by apply Hargs|reflexivity].
- exploit cor_eval; [by apply Hmem_g|by apply Hf|].
  i. inversion x0; subst. by auto.
}
{ simpl run_only. i.
eapply cor_ret_some with (cid:=cid)
; [|eapply cor_eval; [by apply Hmem_g|by apply Hv]|by apply HAbs|by apply Hm'].
eapply cor_remove_local_variables; [by apply Hmem_g|reflexivity].
}
{ simpl run_only. i. rewrite HAbs.
eapply cor_remove_local_variables; [|by apply Hm'].
eapply weaken_mem_g. by apply Hmem_g.
}
{ simpl run_only. i. by rewrite HAbs. }
{ simpl run_only. i. by rewrite HAbs. }
Qed.

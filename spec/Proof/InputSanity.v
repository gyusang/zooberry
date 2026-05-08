(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** Sanity check that a proof module was built over the expected input. *)
Set Implicit Arguments.

Require Import UserInputType.
Require Import UserProofType.

Module Type INPUT_WITH (Expected : INPUT).
Include Expected.
End INPUT_WITH.

Module Make (Expected : INPUT) (Actual : INPUT_WITH Expected).

Definition loc_to_expected (l : Actual.Loc.t) : Expected.Loc.t := l.
Definition loc_to_actual (l : Expected.Loc.t) : Actual.Loc.t := l.

Definition val_to_expected (v : Actual.Val.t) : Expected.Val.t := v.
Definition val_to_actual (v : Expected.Val.t) : Actual.Val.t := v.

Definition powloc_to_expected (lvs : Actual.PowLoc.t) : Expected.PowLoc.t :=
  lvs.
Definition powloc_to_actual (lvs : Expected.PowLoc.t) : Actual.PowLoc.t :=
  lvs.

Definition mem_to_expected (m : Actual.Mem.t) : Expected.Mem.t := m.
Definition mem_to_actual (m : Expected.Mem.t) : Actual.Mem.t := m.

Definition query_to_expected (q : Actual.query) : Expected.query := q.
Definition query_to_actual (q : Expected.query) : Actual.query := q.

Definition status_to_expected (s : Actual.status) : Expected.status := s.
Definition status_to_actual (s : Expected.status) : Actual.status := s.

Definition approx_one_loc_same :
  Expected.approx_one_loc = Actual.approx_one_loc := eq_refl.

Definition collect_query_same :
  Expected.collect_query = Actual.collect_query := eq_refl.

Definition run_only_same :
  Expected.run_only = Actual.run_only := eq_refl.

Definition run_access_same :
  Expected.run_access = Actual.run_access := eq_refl.

End Make.

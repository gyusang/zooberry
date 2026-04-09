(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Set Implicit Arguments.

Require Vali.

Require Coq.extraction.Extraction.
Extraction Language OCaml.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.

Extraction Blacklist String List Nat.

Global Set Warnings "-extraction-opaque-accessed".
Global Set Warnings "-extraction-reserved-identifier".
Global Set Warnings "-extraction-logical-axiom".

(* Separate Extraction Vali. *)
Recursive Extraction Library Vali.

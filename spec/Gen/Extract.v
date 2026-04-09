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

(* Avoid collisions between Coq's decimal/hex/numeral [int] types and
   OCaml's builtin [int] introduced by ExtrOcamlNatInt / ExtrOcamlZInt. *)
Extract Inductive Decimal.int => "signed_int" [ "Pos" "Neg" ].
Extract Inductive Hexadecimal.int => "signed_int" [ "Pos" "Neg" ].
Extract Inductive Numeral.int => "signed_int" [ "IntDec" "IntHex" ].

Global Set Warnings "-extraction-opaque-accessed".
Global Set Warnings "-extraction-reserved-identifier".
Global Set Warnings "-extraction-logical-axiom".

(* Separate Extraction Vali. *)
Recursive Extraction Library Vali.

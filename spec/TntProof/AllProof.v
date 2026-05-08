(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
Require Import UserProofType.
Require SemProof AccProof.
Require UserInput InputSanity.

(* Keep AllProof transparent so InputSanity can see the concrete INPUT. *)
Module AllProof.
Include SemProof.
Include AccProof.
End AllProof.

Module _AllProofTypeCheck : PINPUT := AllProof.
Module _InputSanity := InputSanity.Make UserInput.Input AllProof.

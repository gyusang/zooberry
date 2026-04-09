# Copyright (c) 2017-present,
# Programming Research Laboratory (ROPAS), Seoul National University, Korea
# This software is distributed under the term of the BSD-3 clause license.
BASIC_OBJ := $(wildcard ../Basic/*.vo)
SPEC_OBJ := $(wildcard ../$(SPEC)Input/*.vo)

.PHONY: all ext clean

all: Makefile.coq Vali.v
	$(MAKE) -f Makefile.coq

$(SPEC).current:
	rm -f *.current
	touch $(SPEC).current

Makefile.coq: Makefile $(BASIC_OBJ) $(SPEC_OBJ) $(SPEC).current
	rm -f $(COQ_GEN)
	coq_makefile INSTALLDEFAULTROOT = .. -R ../Basic Basic \
	  -R ../$(SPEC)Input $(SPEC)Input -R . Gen Vali.v -o Makefile.coq

ext: all Extract.v
	coqc -R ../Basic Basic -R ../$(SPEC)Input $(SPEC)Input -R . Gen \
	  Extract.v
	rm -f ../../analyzer/extract/*.ml*
	mv *.ml* ../../analyzer/extract/
	perl -0pi -e 's/type decimal =/\ntype signed_int =\n| Pos of uint\n| Neg of uint\n\ntype decimal =/' ../../analyzer/extract/Decimal.ml ../../analyzer/extract/Decimal.mli
	perl -0pi -e 's/type hexadecimal =/\ntype signed_int =\n| Pos of uint\n| Neg of uint\n\ntype hexadecimal =/' ../../analyzer/extract/Hexadecimal.ml ../../analyzer/extract/Hexadecimal.mli
	perl -0pi -e 's/HexadecimalExp of signed_int \* uint \* signed_int/HexadecimalExp of signed_int * uint * Decimal.signed_int/' ../../analyzer/extract/Hexadecimal.ml ../../analyzer/extract/Hexadecimal.mli
	perl -0pi -e 's/type numeral =/\ntype signed_int =\n| IntDec of Decimal.signed_int\n| IntHex of Hexadecimal.signed_int\n\ntype numeral =/' ../../analyzer/extract/Numeral.ml ../../analyzer/extract/Numeral.mli
	perl -0pi -e 's/val of_int : signed_int/val of_int : Decimal.signed_int/g; s/val of_hex_int : signed_int/val of_hex_int : Hexadecimal.signed_int/g; s/val of_num_int : signed_int/val of_num_int : Numeral.signed_int/g; s/val to_int : int -> signed_int/val to_int : int -> Decimal.signed_int/g; s/val to_hex_int : int -> signed_int/val to_hex_int : int -> Hexadecimal.signed_int/g; s/val to_num_int : int -> signed_int/val to_num_int : int -> Numeral.signed_int/g' ../../analyzer/extract/Nat0.mli ../../analyzer/extract/PeanoNat.mli ../../analyzer/extract/BinPos.mli ../../analyzer/extract/BinPosDef.mli ../../analyzer/extract/BinNat.mli ../../analyzer/extract/BinInt.mli
	perl -0pi -e 's/match Decimal\.norm d with\n    \| Pos u -> Some \(of_uint u\)\n    \| Neg _ -> None/match Decimal.norm d with\n    | Decimal.Pos u -> Some (of_uint u)\n    | Decimal.Neg _ -> None/g; s/match norm d with\n    \| Pos u -> Some \(of_hex_uint u\)\n    \| Neg _ -> None/match norm d with\n    | Hexadecimal.Pos u -> Some (of_hex_uint u)\n    | Hexadecimal.Neg _ -> None/g' ../../analyzer/extract/Nat0.ml ../../analyzer/extract/PeanoNat.ml
	perl -0pi -e 's/let of_int d =\n    match Decimal\.norm d with\n    \| Pos d0 -> Some \(Pos\.of_uint d0\)\n    \| Neg _ -> None/let of_int d =\n    match Decimal.norm d with\n    | Decimal.Pos d0 -> Some (Pos.of_uint d0)\n    | Decimal.Neg _ -> None/g; s/let of_hex_int d =\n    match norm d with\n    \| Pos d0 -> Some \(Pos\.of_hex_uint d0\)\n    \| Neg _ -> None/let of_hex_int d =\n    match norm d with\n    | Hexadecimal.Pos d0 -> Some (Pos.of_hex_uint d0)\n    | Hexadecimal.Neg _ -> None/g' ../../analyzer/extract/BinNat.ml
	perl -0pi -e 's/let of_int = function\n  \| Pos d0 ->\n    \(\(fun f0 fp n -> if n=0 then f0 \(\) else fp n\)\n       \(fun _ -> None\)\n       \(fun p -> Some p\)\n       \(of_uint d0\)\)\n  \| Neg _ -> None/let of_int = function\n  | Decimal.Pos d0 ->\n    ((fun f0 fp n -> if n=0 then f0 () else fp n)\n       (fun _ -> None)\n       (fun p -> Some p)\n       (of_uint d0))\n  | Decimal.Neg _ -> None/g; s/let of_hex_int = function\n  \| Pos d0 ->\n    \(\(fun f0 fp n -> if n=0 then f0 \(\) else fp n\)\n       \(fun _ -> None\)\n       \(fun p -> Some p\)\n       \(of_hex_uint d0\)\)\n  \| Neg _ -> None/let of_hex_int = function\n  | Hexadecimal.Pos d0 ->\n    ((fun f0 fp n -> if n=0 then f0 () else fp n)\n       (fun _ -> None)\n       (fun p -> Some p)\n       (of_hex_uint d0))\n  | Hexadecimal.Neg _ -> None/g' ../../analyzer/extract/BinPos.ml ../../analyzer/extract/BinPosDef.ml
	perl -0pi -e 's/let of_int = function\n  \| Pos d0 -> of_uint d0\n  \| Neg d0 -> opp \(of_uint d0\)/let of_int = function\n  | Decimal.Pos d0 -> of_uint d0\n  | Decimal.Neg d0 -> opp (of_uint d0)/g; s/let of_hex_int = function\n  \| Pos d0 -> of_hex_uint d0\n  \| Neg d0 -> opp \(of_hex_uint d0\)/let of_hex_int = function\n  | Hexadecimal.Pos d0 -> of_hex_uint d0\n  | Hexadecimal.Neg d0 -> opp (of_hex_uint d0)/g' ../../analyzer/extract/BinInt.ml
	perl -0pi -e 's/\| IntDec d0 -> of_int d0/| Numeral.IntDec d0 -> of_int d0/g; s/\| IntHex d0 -> of_hex_int d0/| Numeral.IntHex d0 -> of_hex_int d0/g; s/IntDec \(to_int n\)/Numeral.IntDec (to_int n)/g; s/Pos \(to_uint ([A-Za-z0-9_]+)\)/Decimal.Pos (to_uint $$1)/g; s/Pos \(to_hex_uint ([A-Za-z0-9_]+)\)/Hexadecimal.Pos (to_hex_uint $$1)/g' ../../analyzer/extract/Nat0.ml ../../analyzer/extract/PeanoNat.ml ../../analyzer/extract/BinPos.ml ../../analyzer/extract/BinPosDef.ml ../../analyzer/extract/BinNat.ml
	perl -0pi -e 's/\| IntDec d0 -> of_int d0/| Numeral.IntDec d0 -> of_int d0/g; s/\| IntHex d0 -> of_hex_int d0/| Numeral.IntHex d0 -> of_hex_int d0/g; s/IntDec \(to_int n\)/Numeral.IntDec (to_int n)/g; s/Pos \(Decimal\.D0 Decimal\.Nil\)/Decimal.Pos (Decimal.D0 Decimal.Nil)/g; s/fun p -> Pos \(Pos\.to_uint p\)/fun p -> Decimal.Pos (Pos.to_uint p)/g; s/fun p -> Neg \(Pos\.to_uint p\)/fun p -> Decimal.Neg (Pos.to_uint p)/g; s/Pos \(D0 Nil\)/Hexadecimal.Pos (D0 Nil)/g; s/fun p -> Pos \(Pos\.to_hex_uint p\)/fun p -> Hexadecimal.Pos (Pos.to_hex_uint p)/g; s/fun p -> Neg \(Pos\.to_hex_uint p\)/fun p -> Hexadecimal.Neg (Pos.to_hex_uint p)/g' ../../analyzer/extract/BinInt.ml

clean:
	rm -f $(COQ_GEN)

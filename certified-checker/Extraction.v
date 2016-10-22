Require Export SetChecker.

Extraction Language Ocaml.

Extract Inductive positive => int [ "(fun x -> 2*x+1)" "(fun x -> 2*x)" "1" ]
 "(fun fI fO fH n -> if n=1 then fH () else if n mod 2 = 0 then fO (n/2) else fI (n/2))".
Extract Inlined Constant Pos.compare => "(fun x y -> if x = y then Eq else (if x < y then Lt else Gt))".

Extract Inlined Constant force => "Lazy.force".
Extract Inlined Constant fromVal => "Lazy.from_val".
Extract Constant LazyT "'a" => "'a Lazy.t".

Extraction "Checker" refute.

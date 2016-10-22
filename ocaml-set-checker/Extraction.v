Require Export SetChecker.

Extraction Language Ocaml.

Extract Inductive positive => int [ "(fun x -> 2*x+1)" "(fun x -> 2*x)" "1" ]
 "(fun fI fO fH n -> if n=1 then fH () else if n mod 2 = 0 then fO (n/2) else fI (n/2))".
Extract Inlined Constant Pos.compare => "(fun x y -> if x = y then Eq else (if x < y then Lt else Gt))".

Extract Inlined Constant force => "Lazy.force".
Extract Inlined Constant fromVal => "Lazy.from_val".
Extract Constant LazyT "'a" => "'a Lazy.t".

Extract Constant CNF => "SetOfClauses.t".
Extract Inlined Constant CNF_empty_constant => "SetOfClauses.empty".
Extract Inlined Constant CNF_add => "SetOfClauses.add".
Extract Inlined Constant BT_in_dec => "(fun _ cl c -> if SetOfClauses.mem cl c then Left else Right)".

Extract Constant SetClause => "SetOfLiterals.t".
Extract Inlined Constant SC_add => "SetOfLiterals.add".
Extract Inlined Constant SC_diff => "SetOfLiterals.diff".
Extract Inlined Constant SC_empty => "SetOfLiterals.empty".
Extract Constant Clause_to_SetClause => "function
| Nil -> SetOfLiterals.empty
| Cons (l, cl') -> SetOfLiterals.add l (clause_to_SetClause cl')".
Extract Constant true_SC => "SetOfLiterals.add (Pos 1) (SetOfLiterals.add (Neg 1) SetOfLiterals.empty)".
Extract Constant SetClause_eq_nil_cons => "(fun c -> if SetOfLiterals.is_empty c then Inright else let m = SetOfLiterals.min_elt c in Inleft (ExistT (m, (ExistT (SetOfLiterals.remove m c, SetOfLiterals.empty)))))".

Extraction "Checker" refute.

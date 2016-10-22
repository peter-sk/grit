type action = D of int list | O of int * int list | R of int * int list * int list

let nat_to_N = function
| 0 -> Checker.N0
| n -> Checker.Npos n

let rec list_to_List = function
| [] -> Checker.Nil
| x :: l -> Checker.Cons (x,list_to_List l)

let literal_to_Literal = function
| x -> if x > 0 then Checker.Pos x else Checker.Neg (-x)

let (<<) f g x = f(g(x));;

let clause_to_Clause = list_to_List << List.map literal_to_Literal

let action_to_Action = function
| D is -> Checker.D (list_to_List (List.map nat_to_N is))
| O (i,c) -> Checker.O0 (nat_to_N i,clause_to_Clause c)
| R (i,c,is) -> Checker.R (nat_to_N i,clause_to_Clause c,list_to_List (List.map nat_to_N is))

let test = Checker.refute

let rec lines = function
| chan -> try
    let line = input_line chan in let rest = lines chan in
      if line = "" then rest else line :: rest
  with End_of_file ->
    close_in chan;
    []

let words = List.filter ((<>) "") << Str.split (Str.regexp " ")

exception Should_never_happen of string 

let rec drop_zero = function
| [0] -> []
| x::xs -> x::drop_zero xs
| [] -> raise (Should_never_happen "clause not terminated with 0")

let rec extract_clauses = function
| [] -> []
| line::lines -> let rest = extract_clauses lines in match (Str.first_chars line 1) with
  | "c" -> rest
  | "p" -> rest
  | _ -> line::rest

let rec take n l = if n = 0 then [] else List.hd l::take (n-1) (List.tl l)

let rec drop n l = if n = 0 then l else drop (n-1) (List.tl l)

let rec treeify l = let ll = List.length l in if ll = 0 then [] else let k = ll / 2 in
  (List.nth l k)::List.append (treeify (take k l)) (treeify (drop (k+1) l))

let parse_cnf = list_to_List << List.map clause_to_Clause << List.map (treeify << (List.sort compare)) << List.map drop_zero << (List.filter ((<>) [])) << (List.map (List.map int_of_string << words)) << extract_clauses << lines

let read_cnf = function
| name -> let chan = open_in name in
  parse_cnf chan

let rec split_zero = function
| 0::xs -> [],drop_zero xs
| x::xs -> let ys,zs = split_zero xs in x::ys,zs
| [] -> raise (Should_never_happen "action not terminated with 0")

let list_to_action = function
| 0::xs -> D (drop_zero xs)
| id::xs -> let ys,zs = split_zero xs in let sorted_ys = treeify (List.sort compare ys) in
    if zs = [] then O (id,sorted_ys) else R (id,sorted_ys,zs)
| [] -> raise (Should_never_happen "empty action")

let rec lazy_lines chan =
  match try Some (input_line chan) with End_of_file -> (close_in chan; None) with
  | Some line -> lazy (Checker.Lcons (line,lazy_lines chan))
  | None -> lazy Checker.Lnil

let rec lazy_map f l = match Lazy.force l with
| Checker.Lnil -> lazy Checker.Lnil
| Checker.Lcons (x,xs) -> lazy (Checker.Lcons (f x,lazy_map f xs))

let rec lazy_filter p l = match Lazy.force l with
| Checker.Lnil -> lazy Checker.Lnil
| Checker.Lcons (x,xs) -> if p x then lazy (Checker.Lcons (x,lazy_filter p xs)) else lazy_filter p xs

let parse_grup = (lazy_map action_to_Action) << (lazy_map list_to_action) << (lazy_filter ((<>) [])) << (lazy_map (List.map int_of_string << words)) << lazy_lines

let read_grup = function
| name -> let chan = open_in name in
  parse_grup chan

let () = 
  let cnfFile = Sys.argv.(1) in
  let cnf = read_cnf cnfFile in
  let grupFile = Sys.argv.(2) in
  let grup = read_grup grupFile in
  if test cnf grup == Checker.True then print_endline "True" else print_endline "False"


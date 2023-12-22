#use "MyOCaml.ml";;
#use "interp.ml";;
(* abstract syntax tree of high-level language *)

type uopr =
  | Neg | Not

type bopr =
  | Add | Sub | Mul | Div | Mod
  | And | Or
  | Lt  | Gt  | Lte | Gte | Eq

type expr =
  | Int of int
  | Bool of bool
  | Unit
  | UOpr of uopr * expr
  | BOpr of bopr * expr * expr
  | Var of string
  | Fun of string * string * expr
  | App of expr * expr
  | Let of string * expr * expr
  | Seq of expr * expr
  | Ifte of expr * expr * expr
  | Trace of expr

(* ------------------------------------------------------------ *)

(* combinator for left-associative operators *)

let chain_left (p : 'a parser) (q : ('a -> 'a -> 'a) parser) : 'a parser =
  let* init = p in
  let* fms = many (let* f = q in let* m = p in pure (f, m)) in
  let m = list_foldleft fms init (fun acc (f, m) -> f acc m) in
  pure m

let rec chain_right (p : 'a parser) (q : ('a -> 'a -> 'a) parser) : 'a parser =
  let* m = p in
  (let* f = q in
   let* rest = chain_right p q in
   pure (f m rest)) <|> 
  (pure m)

let opt (p : 'a parser) : 'a option parser =
  (let* x = p in pure (Some x)) <|> pure None

(* basic constants *)

let parse_int : expr parser =
  let* n = natural in
  pure (Int n) << whitespaces

let parse_bool : expr parser =
  (keyword "true" >> pure (Bool true)) <|>
  (keyword "false" >> pure (Bool false))

let parse_unit : expr parser =
  keyword "(" >> keyword ")" >> pure Unit

(* names *)

let isReserved s =
  let reserved = 
    ["let"; "rec"; "in"; "fun"; "if"; "then"; "else"; "trace"; "mod"; "not"] 
  in
  list_exists reserved (fun s0 -> s0 = s)

let parse_name : string parser =
  let lower = satisfy char_islower in
  let upper = satisfy char_isupper in
  let digit = satisfy char_isdigit in
  let quote = char '\'' in
  let wildc = char '_' in
  let* c = lower <|> wildc in
  let* cs = many (lower <|> upper <|> digit <|> wildc <|> quote) in
  let s = string_make_fwork (list_foreach (c :: cs)) in
  if isReserved s then fail
  else pure s << whitespaces

(* unary operators *)

let parse_neg : (expr -> expr) parser =
  keyword "-" >> pure (fun m -> UOpr (Neg, m))

(* binary operators *)

let parse_add : (expr -> expr -> expr) parser =
  keyword "+" >> pure (fun m n -> BOpr (Add, m, n))

let parse_sub : (expr -> expr -> expr) parser =
  keyword "-" >> pure (fun m n -> BOpr (Sub, m, n))

let parse_mul : (expr -> expr -> expr) parser =
  keyword "*" >> pure (fun m n -> BOpr (Mul, m, n))

let parse_div : (expr -> expr -> expr) parser =
  keyword "/" >> pure (fun m n -> BOpr (Div, m, n))

let parse_mod : (expr -> expr -> expr) parser =
  keyword "mod" >> pure (fun m n -> BOpr (Mod, m, n))

let parse_and : (expr -> expr -> expr) parser =
  keyword "&&" >> pure (fun m n -> BOpr (And, m, n))

let parse_or : (expr -> expr -> expr) parser =
  keyword "||" >> pure (fun m n -> BOpr (Or, m, n))

let parse_lt : (expr -> expr -> expr) parser =
  keyword "<" >> pure (fun m n -> BOpr (Lt, m, n))

let parse_gt : (expr -> expr -> expr) parser =
  keyword ">" >> pure (fun m n -> BOpr (Gt, m, n))

let parse_lte : (expr -> expr -> expr) parser =
  keyword "<=" >> pure (fun m n -> BOpr (Lte, m, n))

let parse_gte : (expr -> expr -> expr) parser =
  keyword ">=" >> pure (fun m n -> BOpr (Gte, m, n))

let parse_eq : (expr -> expr -> expr) parser =
  keyword "=" >> pure (fun m n -> BOpr (Eq, m, n))

let parse_neq : (expr -> expr -> expr) parser =
  keyword "<>" >> pure (fun m n -> UOpr (Not, BOpr (Eq, m, n)))

let parse_seq : (expr -> expr -> expr) parser =
  keyword ";" >> pure (fun m n -> Seq (m, n))

(* expression parsing *)

let rec parse_expr () = 
  let* _ = pure () in
  parse_expr9 ()

and parse_expr1 () : expr parser = 
  let* _ = pure () in
  parse_int <|> 
  parse_bool <|> 
  parse_unit <|>
  parse_var () <|>
  parse_fun () <|>
  parse_letrec () <|>
  parse_let () <|>
  parse_ifte () <|>
  parse_trace () <|>
  parse_not () <|>
  (keyword "(" >> parse_expr () << keyword ")")

and parse_expr2 () : expr parser =
  let* m = parse_expr1 () in
  let* ms = many' parse_expr1 in
  let m = list_foldleft ms m (fun acc m -> App (acc, m)) in
  pure m

and parse_expr3 () : expr parser =
  let* f_opt = opt parse_neg in
  let* m = parse_expr2 () in
  match f_opt with
  | Some f -> pure (f m)
  | None -> pure m

and parse_expr4 () : expr parser =
  let opr = parse_mul <|> parse_div <|> parse_mod in
  chain_left (parse_expr3 ()) opr

and parse_expr5 () : expr parser =
  let opr = parse_add <|> parse_sub in
  chain_left (parse_expr4 ()) opr

and parse_expr6 () : expr parser =
  let opr = 
    parse_lte <|> 
    parse_gte <|>
    parse_neq <|>
    parse_lt <|> 
    parse_gt <|>
    parse_eq
  in
  chain_left (parse_expr5 ()) opr

and parse_expr7 () : expr parser =
  chain_left (parse_expr6 ()) parse_and

and parse_expr8 () : expr parser =
  chain_left (parse_expr7 ()) parse_or

and parse_expr9 () : expr parser =
  chain_right (parse_expr8 ()) parse_seq

and parse_var () : expr parser =
  let* x = parse_name in
  pure (Var x)

and parse_fun () : expr parser =
  let* _ = keyword "fun" in
  let* xs = many1 parse_name in 
  let* _ = keyword "->" in
  let* body = parse_expr () in
  let m = list_foldright xs body (fun x acc -> Fun ("", x, acc)) in
  pure m

and parse_let () : expr parser =
  let* _ = keyword "let" in
  let* x = parse_name in
  let* xs = many parse_name in
  let* _ = keyword "=" in
  let* body = parse_expr () in
  let* _ = keyword "in" in
  let* n = parse_expr () in
  let m = list_foldright xs body (fun x acc -> Fun ("", x, acc)) in
  pure (Let (x, m, n))

and parse_letrec () : expr parser =
  let* _ = keyword "let" in
  let* _ = keyword "rec" in
  let* f = parse_name in
  let* x = parse_name in
  let* xs = many parse_name in
  let* _ = keyword "=" in
  let* body = parse_expr () in
  let* _ = keyword "in" in
  let* n = parse_expr () in
  let m = list_foldright xs body (fun x acc -> Fun ("", x, acc)) in
  pure (Let (f, Fun (f, x, m), n))

and parse_ifte () : expr parser =
  let* _ = keyword "if" in
  let* m = parse_expr () in
  let* _ = keyword "then" in
  let* n1 = parse_expr () in
  let* _ = keyword "else" in
  let* n2 = parse_expr () in
  pure (Ifte (m, n1, n2))

and parse_trace () : expr parser =
  let* _ = keyword "trace" in
  let* m = parse_expr1 () in
  pure (Trace m) 

and parse_not () : expr parser =
  let* _ = keyword "not" in
  let* m = parse_expr1 () in
  pure (UOpr (Not, m))

exception SyntaxError
exception UnboundVariable of string

type scope = (string * string) list

let new_var =
  let stamp = ref 0 in
  fun x ->
    incr stamp;
    let xvar = string_filter x (fun c -> c <> '_' && c <> '\'') in
    string_concat_list ["v"; xvar; "i"; string_of_int !stamp]

let find_var scope s =
  let rec loop scope =
    match scope with
    | [] -> None
    | (s0, x) :: scope ->
      if s = s0 then Some x
      else loop scope
  in loop scope

let scope_expr (m : expr) : expr = 
  let rec aux scope m =
    match m with
    | Int i -> Int i
    | Bool b -> Bool b
    | Unit -> Unit
    | UOpr (opr, m) -> UOpr (opr, aux scope m)
    | BOpr (opr, m, n) -> 
      let m = aux scope m in
      let n = aux scope n in
      BOpr (opr, m, n)
    | Var s -> 
      (match find_var scope s with
       | None -> raise (UnboundVariable s)
       | Some x -> Var x)
    | Fun (f, x, m) -> 
      let fvar = new_var f in
      let xvar = new_var x in
      let m = aux ((f, fvar) :: (x, xvar) :: scope) m in
      Fun (fvar, xvar, m)
    | App (m, n) ->
      let m = aux scope m in
      let n = aux scope n in
      App (m, n)
    | Let (x, m, n) ->
      let xvar = new_var x in
      let m = aux scope m in
      let n = aux ((x, xvar) :: scope) n in
      Let (xvar, m, n)
    | Seq (m, n) ->
      let m = aux scope m in
      let n = aux scope n in
      Seq (m, n)
    | Ifte (m, n1, n2) ->
      let m = aux scope m in
      let n1 = aux scope n1 in
      let n2 = aux scope n2 in
      Ifte (m, n1, n2)
    | Trace m -> Trace (aux scope m)
  in
  aux [] m

(* ------------------------------------------------------------ *)

(* parser for the high-level language *)

let parse_prog (s : string) : expr =
  match string_parse (whitespaces >> parse_expr ()) s with
  | Some (m, []) -> scope_expr m
  | _ -> raise SyntaxError

let (@) = list_append
let(^) = string_append

let rec coms_of_ex (e: expr) : coms =
  match e with
  | Int x -> [Push (Int x);]
  | Bool x -> [Push (Bool x);]
  | Unit -> [Push (Unit);]
  | Var x -> [Push (Sym x); Lookup;]
  (* UOpr CASES -------------------------------------------------------------------------------------------------------------*)
  | UOpr (Neg, ex) -> (coms_of_ex ex) @ [Push (Int 0); Sub;]
  | UOpr (Not, ex) -> (coms_of_ex ex) @ [Not;]
  (* BOpr CASES -------------------------------------------------------------------------------------------------------------*)
  | BOpr (Add, ex1, ex2) -> (coms_of_ex ex1) @ (coms_of_ex ex2) @ [Add;]
  | BOpr (Sub, ex1, ex2) -> (coms_of_ex ex1) @ (coms_of_ex ex2) @ [Swap; Sub;]
  | BOpr (Mul, ex1, ex2) -> (coms_of_ex ex1) @ (coms_of_ex ex2) @ [Mul;]
  | BOpr (Div, ex1, ex2) -> (coms_of_ex ex1) @ (coms_of_ex ex2) @ [Swap; Div;]
  | BOpr (Mod, ex1, ex2) -> coms_of_ex (BOpr(Sub, ex1, BOpr(Mul, ex2, BOpr(Div, ex1, ex2)))) 
  | BOpr (And, ex1, ex2) -> (coms_of_ex ex1) @ (coms_of_ex ex2) @ [And;]
  | BOpr (Or, ex1, ex2) -> (coms_of_ex ex1) @ (coms_of_ex ex2) @ [Or;]
  | BOpr (Lt, ex1, ex2) -> (coms_of_ex ex1) @ (coms_of_ex ex2) @ [Swap; Lt;]
  | BOpr (Gt, ex1, ex2) -> (coms_of_ex ex1) @ (coms_of_ex ex2) @ [Swap; Gt;]
  | BOpr (Lte, ex1, ex2) -> coms_of_ex (BOpr(Or, BOpr(Lt, ex1, ex2), BOpr(Eq, ex1, ex2)))
  | BOpr (Gte, ex1, ex2) -> coms_of_ex (BOpr(Or, BOpr(Gt, ex1, ex2), BOpr(Eq, ex1, ex2)))
  | BOpr (Eq, ex1, ex2) -> coms_of_ex (BOpr(And, UOpr(Not, BOpr(Lt, ex1, ex2)), UOpr(Not, BOpr(Gt, ex1, ex2))))
  | Fun (s1, s2, ex) -> let var = [Push (Sym s2); Bind;] @ (coms_of_ex ex) @ [Swap; Return;] in [Push (Sym s1); Fun (var);]
  | App (ex1, ex2) -> (coms_of_ex ex1) @ (coms_of_ex ex2) @ [Swap; Call;]
  | Let (x, ex1, ex2) -> (coms_of_ex ex1) @ [Push (Sym x); Bind;] @ (coms_of_ex ex2)
  | Seq (ex1, ex2) -> (coms_of_ex ex1) @ (coms_of_ex ex2)
  | Ifte (ex1, ex2, ex3) -> (coms_of_ex ex1) @ [Ifelse ((coms_of_ex ex2), (coms_of_ex ex3));]
  | Trace ex -> (coms_of_ex ex) @ [Trace; Pop;]   (*Removing the pop command will make one case work but break other cases*)

let format_string_of_list (xs: 'a list): string =
  string_concat_list (list_reverse xs)
  
let rec coms_to_slist (cs: coms) (s_list: string list): string list =
  match cs with
  | [] -> s_list
  | Push c :: cs0 -> let com = "Push " ^ (toString c) ^ "; " in coms_to_slist cs0 (com :: s_list)
  | Pop :: cs0 -> let com = "Pop; " in coms_to_slist cs0 (com :: s_list)
  | Swap :: cs0 -> let com = "Swap; " in coms_to_slist cs0 (com :: s_list)
  | Trace :: cs0 -> let com = "Trace; " in coms_to_slist cs0 (com :: s_list)
  | Add :: cs0 -> let com = "Add; " in coms_to_slist cs0 (com :: s_list)
  | Sub :: cs0 -> let com = "Sub; " in coms_to_slist cs0 (com :: s_list)
  | Mul :: cs0 -> let com = "Mul; " in coms_to_slist cs0 (com :: s_list)
  | Div :: cs0 -> let com = "Div; " in coms_to_slist cs0 (com :: s_list)
  | And :: cs0 -> let com = "And; " in coms_to_slist cs0 (com :: s_list)
  | Or :: cs0 -> let com = "Or; " in coms_to_slist cs0 (com :: s_list)
  | Not :: cs0 -> let com = "Not; " in coms_to_slist cs0 (com :: s_list)
  | Lt :: cs0 -> let com = "Lt; " in coms_to_slist cs0 (com :: s_list)
  | Gt :: cs0 -> let com = "Gt; " in coms_to_slist cs0 (com :: s_list)
  | Ifelse (c1, c2) :: cs0 -> let com = "If " ^ (format_string_of_list (coms_to_slist c1 [])) ^ " Else " ^ (format_string_of_list(coms_to_slist c2 [])) ^ "End; " in coms_to_slist cs0 (com :: s_list)
  | Bind :: cs0 -> let com = "Bind; " in coms_to_slist cs0 (com :: s_list)
  | Lookup :: cs0 -> let com = "Lookup; " in coms_to_slist cs0 (com :: s_list)
  | Fun c :: cs0 -> let com = "Fun " ^ (format_string_of_list (coms_to_slist c [])) ^ "End; " in 
  coms_to_slist cs0 (com :: s_list)
  | Call :: cs0 -> let com = "Call; " in coms_to_slist cs0 (com :: s_list)
  | Return :: cs0 -> let com = "Return; " in coms_to_slist cs0 (com :: s_list)

let compile (s : string) : string = 
  let parsed_expr = parse_prog s in
  let compiled_coms_list = coms_of_ex parsed_expr in
  format_string_of_list (coms_to_slist compiled_coms_list [])
  
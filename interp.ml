#use "./../../../classlib/OCaml/MyOCaml.ml";;

(* abstract syntax tree *)
type const =
  | Int of int
  | Bool of bool
  | Unit
  | Sym of string
  | Closure of (string * ((string * const) list) * com list)

and com =
  | Push of const | Pop | Swap | Trace
  | Add | Sub | Mul | Div
  | And | Or | Not
  | Lt | Gt
  | Ifelse of com list * com list | Bind | Lookup | Fun of com list | Call | Return

and coms = com list



(* ------------------------------------------------------------ *)

(* parsers for interp1 *)
let parse_nat = 
  let* n = natural << whitespaces in pure n

let parse_int =
  (let* n = parse_nat in pure (Int n)) <|>
  (keyword "-" >> let* n = parse_nat in pure (Int (-n)))

let parse_bool =
  (keyword "True" >> pure (Bool true)) <|>
  (keyword "False" >> pure (Bool false))

let parse_unit =
  keyword "Unit" >> pure Unit

(* Interpreter 2 *)

let parse_char =
   satisfy char_islower

let parse_digit = 
   satisfy char_isdigit

let parse_char_or_int = 
   parse_char <|> parse_digit 

let string_of_list xs = 
   string_make_fwork (list_foreach xs)

let parse_sym =
   (let* first = parse_char in
   let* rest = many(parse_char_or_int) in
   let str = string_append (str first) (string_of_list rest) in
   pure(Sym str)) 

let parse_const =
  parse_int <|>
  parse_bool <|>
  parse_unit <|>
  parse_sym

let rec parse_com () = 
  (keyword "Push" >> parse_const >>= fun c -> pure (Push c)) <|>
  (keyword "Pop" >> pure Pop) <|>
  (keyword "Swap" >> pure Swap) <|>
  (keyword "Trace" >> pure Trace) <|>
  (keyword "Add" >> pure Add) <|>
  (keyword "Sub" >> pure Sub) <|>
  (keyword "Mul" >> pure Mul) <|>
  (keyword "Div" >> pure Div) <|>
  (keyword "And" >> pure And) <|>
  (keyword "Or" >> pure Or) <|>
  (keyword "Not" >> pure Not) <|>
  (keyword "Lt" >> pure Lt) <|>
  (keyword "Gt" >> pure Gt) <|>
  (let* _ = keyword "If" in
   let* com_one = many (parse_com () << keyword ";") in
   let* _ = keyword "Else" in
   let* com_two = many (parse_com () << keyword ";") in
   let* _ = keyword "End" in
   pure (Ifelse(com_one, com_two))) <|>
  (keyword "Bind" >> pure Bind) <|>
  (keyword "Lookup" >> pure Lookup) <|>
  (let* _ = keyword "Fun" in
   let* com = many (parse_com () << keyword ";") in
   let* _ = keyword "End" in
   pure (Fun com)) <|>
  (keyword "Call" >> pure Call) <|>
  (keyword "Return" >> pure Return)

let parse_coms = many (parse_com () << keyword ";")

(* and parse_Ifelse = *)
   


(* ------------------------------------------------------------ *)

(* interpreter *)

type stack = const list
type trace = string list
type prog = coms
type environment = (string * const) list

let rec str_of_nat (n : int) : string =
  let d = n mod 10 in 
  let n0 = n / 10 in
  let s = str (chr (d + ord '0')) in 
  if 0 < n0 then
    string_append (str_of_nat n0) s
  else s

let str_of_int (n : int) : string = 
  if n < 0 then
    string_append "-" (str_of_nat (-n))
  else str_of_nat n

let toString (c : const) : string =
  match c with
  | Int i -> str_of_int i
  | Bool true -> "True"
  | Bool false -> "False"
  | Unit -> "Unit"
  | Sym c -> c
  | Closure (name, env, coms) -> string_concat_list ["Fun<";name;">"]

let rec eval (s : stack) (t : trace) (v : environment) (p : prog) : trace =
  match p with
  (* termination state returns the trace *)
   | [] -> t
   | Push c :: p0 (* PushStack *) -> eval (c :: s) t v p0
   | Pop :: p0 ->
    (match s with
      | _ :: s0 (* PopStack *) -> eval s0 t v p0
      | []      (* PopError *) -> eval [] ("Panic" :: t) [] [])
   | Swap :: p0 ->
      (match s with
      | c1 :: c2 :: s0 -> eval (c2::c1::s0) t v p0
      | [] -> eval [] ("Panic"::t) [] []
      | _ :: [] -> eval [] ("Panic"::t) [] [])
   | Trace :: p0 ->
    (match s with
      | c :: s0 (* TraceStack *) -> eval (Unit :: s0) (toString c :: t) v p0
      | []      (* TraceError *) -> eval [] ("Panic" :: t) [] [])
   | Add :: p0 ->
    (match s with
      | Int i :: Int j :: s0 (* AddStack *)  -> eval (Int (i + j) :: s0) t v p0
      | _ :: _ :: s0         (* AddError1 *) -> eval [] ("Panic" :: t) [] []
      | []                   (* AddError2 *) -> eval [] ("Panic" :: t) [] []
      | _ :: []              (* AddError3 *) -> eval [] ("Panic" :: t) [] [])
   | Sub :: p0 ->
    (match s with
      | Int i :: Int j :: s0 (* SubStack *)  -> eval (Int (i - j) :: s0) t v p0
      | _ :: _ :: s0         (* SubError1 *) -> eval [] ("Panic" :: t) [] []
      | []                   (* SubError2 *) -> eval [] ("Panic" :: t) [] []
      | _ :: []              (* SubError3 *) -> eval [] ("Panic" :: t) [] [])
   | Mul :: p0 ->
    (match s with
      | Int i :: Int j :: s0 (* MulStack *)  -> eval (Int (i * j) :: s0) t v p0
      | _ :: _ :: s0         (* MulError1 *) -> eval [] ("Panic" :: t) [] []
      | []                   (* MulError2 *) -> eval [] ("Panic" :: t) [] []
      | _ :: []              (* MulError3 *) -> eval [] ("Panic" :: t) [] [])
   | Div :: p0 ->
    (match s with
      | Int i :: Int 0 :: s0 (* DivError0 *) -> eval [] ("Panic" :: t) [] []
      | Int i :: Int j :: s0 (* DivStack *)  -> eval (Int (i / j) :: s0) t v p0
      | _ :: _ :: s0         (* DivError1 *) -> eval [] ("Panic" :: t) [] []
      | []                   (* DivError2 *) -> eval [] ("Panic" :: t) [] []
      | _ :: []              (* DivError3 *) -> eval [] ("Panic" :: t) [] [])
   | And :: p0 ->
    (match s with
      | Bool a :: Bool b :: s0 (* AndStack *)  -> eval (Bool (a && b) :: s0) t v p0
      | _ :: _ :: s0           (* AndError1 *) -> eval [] ("Panic" :: t) [] []
      | []                     (* AndError2 *) -> eval [] ("Panic" :: t) [] []
      | _ :: []                (* AndError3 *) -> eval [] ("Panic" :: t) [] [])
   | Or :: p0 ->
    (match s with
      | Bool a :: Bool b :: s0 (* OrStack *)  -> eval (Bool (a || b) :: s0) t v p0
      | _ :: _ :: s0           (* OrError1 *) -> eval [] ("Panic" :: t) [] []
      | []                     (* OrError2 *) -> eval [] ("Panic" :: t) [] []
      | _ :: []                (* OrError3 *) -> eval [] ("Panic" :: t) [] [])
   | Not :: p0 ->
    (match s with
      | Bool a :: s0 (* NotStack  *) -> eval (Bool (not a) :: s0) t v p0
      | _ :: s0      (* NotError1 *) -> eval [] ("Panic" :: t) [] []
      | []           (* NotError2 *) -> eval [] ("Panic" :: t) [] [])
   | Lt :: p0 ->
    (match s with
      | Int i :: Int j :: s0 (* LtStack *)  -> eval (Bool (i < j) :: s0) t v p0
      | _ :: _ :: s0         (* LtError1 *) -> eval [] ("Panic" :: t) [] []
      | []                   (* LtError2 *) -> eval [] ("Panic" :: t) [] []
      | _ :: []              (* LtError3 *) -> eval [] ("Panic" :: t) [] [])
   | Gt :: p0 ->
    (match s with
      | Int i :: Int j :: s0 (* GtStack *)  -> eval (Bool (i > j) :: s0) t v p0
      | _ :: _ :: s0         (* GtError1 *) -> eval [] ("Panic" :: t) [] []
      | []                   (* GtError2 *) -> eval [] ("Panic" :: t) [] []
      | _ :: []              (* GtError3 *) -> eval [] ("Panic" :: t) [] [])
    | Ifelse (c1, c2) :: p0 -> 
      (match s with
      | Bool true :: s0 -> eval s0 t v (list_append c1 p0)
      | Bool false :: s0 -> eval s0 t v (list_append c2 p0)   
      | _ :: s0 -> eval [] ("Panic" :: t) [] []
      | [] -> eval [] ("Panic" :: t) [] [])
   | Bind :: p0 -> 
      (match s with
      | Sym name :: value :: s0 -> eval s0 t ((name, value)::v) p0
      | [] -> eval [] ("Panic" :: t) [] []
      | _ :: [] -> eval [] ("Panic" :: t) [] []
      | _ :: _ :: s0 -> eval [] ("Panic" :: t) [] [])
    | Lookup :: p0 ->
      (match s with
      | Sym name :: s0 -> let rec env_lookup vs = 
                              (match vs with
                              | [] -> eval [] ("TEST3" :: t) [] []
                              | (n, value)::rst -> if n = name then eval (value::s0) t v p0 
                                                   else env_lookup rst)
                          in env_lookup v
      | [] -> eval [] ("Panic" :: t) [] []
      | _ :: s0 -> eval [] ("Panic" :: t) [] [])
    | Fun c :: p0 -> 
      (match s with
      | Sym name :: s0 -> eval (Closure (name, v, c) :: s0) t v p0
      | [] -> eval [] ("Panic" :: t) [] []
      | _ :: s0 -> eval [] ("Panic" :: t) [] [])
    | Call :: p0 -> 
      (match s with
      | Closure (f, vf, c) :: a :: s0 -> let env = (f, Closure (f, vf, c)) :: vf in
                                          eval (a :: Closure ("cc", v, p0) :: s0) t env c
      | [] -> eval [] ("Panic" :: t) [] []
      | _ :: [] -> eval [] ("Panic" :: t) [] []
      | _ :: _ :: [] -> eval [] ("Panic" :: t) [] []
      | _ -> eval [] ("Panic" :: t) [] [])
    | Return :: p0 -> 
      (match s with
      | Closure (f, vf, c) :: a :: s0 -> eval (a :: s0) t vf c
      | [] -> eval [] ("Panic" :: t) [] []
      | _ :: [] -> eval [] ("Panic" :: t) [] []
      | _ -> eval [] ("Panic" :: t) [] [])
    
   

(* ------------------------------------------------------------ *)

(* putting it all together [input -> parser -> eval -> output] *)

let interp (s : string) : string list option =
  match string_parse (whitespaces >> parse_coms) s with
  | Some (p, []) -> Some (eval [] [] [] p)
  (* | Some (p, []) -> Some p *)
  | _ -> None

let parse_str (s: string): com list option =
  match string_parse (whitespaces >> parse_coms) s with
  (* | Some (p, []) -> Some (eval [] [] [] p) *)
  | Some (p, []) -> Some p
  | _ -> None

(* ------------------------------------------------------------ *)

(* interp from file *)
(* 
let read_file (fname : string) : string =
  let fp = open_in fname in
  let s = string_make_fwork (fun work ->
      try
        while true do
          work (input_char fp)
        done
      with _ -> ())
  in
  close_in fp; s

let interp_file (fname : string) : string list option =
  let src = read_file fname in
  interp src *)
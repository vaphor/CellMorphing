(*In this file, we simplify expressions (we remove tuples, ...) *)

open Types
open Helper

(*Removes tuple types from a lst of types.
  Formally it linearlizes all tuples. 
  For example, [Int, Tuple(Int, Tuple(Bool, Int)), Int]
  becomes [Int, Int, Bool, Int, Int]*)
let rec remove_tuple_ltype l = 
  List.flatten (List.map (fun t -> match t with
                                   | TupleT(l) -> remove_tuple_ltype (List.map fst l)
                                   | _ -> [remove_tuple_type t]) l)

(*Linearlizes tuples within a parametrized expression*)
and remove_tuple_type t =
  match t with
  | Basic(str) -> Basic(str)
  | Parametrized(l) -> Parametrized(remove_tuple_ltype l)
  | TupleT(l) -> failwith "tuple type not in a parametrized"


(*Returns the variables created by the expansion of a tuple*)
let name_variables v = 
  match v.vtype with
  | TupleT(l) -> List.mapi (fun i t -> {vname = Printf.sprintf "%s%s" v.vname (match snd t with
                                                                                | None -> if List.length l > 1 then Printf.sprintf "%i" i else ""
                                                                                | Some(suffix) -> Printf.sprintf "_%s" suffix); vtype = fst t}) l
  | _ -> [v]

(*Expands all tuple variables in the map of local variables*)
let expand_variable_tuples lv =
  SMap.fold (fun name var newmap -> let rec get_expansion v = 
                                      match v.vtype with
                                      | TupleT(_) -> List.flatten (List.map get_expansion (name_variables v))
                                      | _ -> [v] 
                                      in
                                    let l = get_expansion var in
                                    List.fold_left (fun rmap nv -> SMap.add nv.vname nv rmap) newmap l)
            lv SMap.empty

(*Remove all tuples from an expression.
  Note that the recursion is done through exprMap*)
let remove_tuple_expr e =
  (*Transforms tuple variables into tuples expressions*)
  let rec remove_tuple_var exp = match exp with
                            | Variable(v) -> begin match v.vtype with
                                             | TupleT(l) -> TupleE(List.map (fun x -> remove_tuple_var (Variable(x))) (name_variables v))
                                             | _ -> exp
                                             end
                            | _ -> exp
                            in
  let var_removed_exp = exprMap remove_tuple_var e in

  let rec remove_tuple_eq exp = match exp with
                                | Composition(Interpreted("=")::TupleE(t1)::TupleE(t2)::[]) 
                                   -> andExpr (listCreate (fun i -> (Composition(Interpreted("=")::Extract(TupleE(t1), i)::Extract(TupleE(t2),i)::[]))) (List.length t1))
                                | _ -> exp
                                in
  let eq_removed_exp = exprMap remove_tuple_eq var_removed_exp in
  (*Applies extract expression*)
  let rec remove_extract exp = match exp with
                                | Extract(TupleE(l), i) -> if List.length l <= i then failwith (Printf.sprintf "Invalid extract id in %s" (printExpr exp));
                                                      List.nth l i
                                | _ -> exp
                                in



  let extract_removed_expr = exprMap remove_extract eq_removed_exp in
  (*Now removes tuples by linearlizing them :
    Expressions taking an undefined number of parameters have the tuples in each of these parameters linearlized*)
  let remove_tuple_expr exp = let flatten_args l = List.flatten (List.map (fun e -> match e with 
                                                                                   | TupleE(tuple) -> tuple
                                                                                   | _ -> [e]) l) in
                              match exp with
                              | Composition(l) -> Composition(flatten_args l)
                              | Predicate(f, l) -> Predicate(f, flatten_args l)
                              | TupleE(l) -> TupleE(flatten_args l)
                              | AbstractOp(str, l) -> AbstractOp(str, flatten_args l)
                              | _ -> exp
                              in
  exprMap remove_tuple_expr extract_removed_expr

(*Removes all tuples from the horn problem*)
let remove_tuples horn =
  {used_predicates = horn.used_predicates;
   commands = List.map 
     (fun command -> try match command with
     | Fundecl(f) -> Fundecl({fname = f.fname; params = remove_tuple_ltype f.params; return = remove_tuple_type f.return})
     | Clause(lv, conds, res) -> Clause(expand_variable_tuples lv, List.map remove_tuple_expr conds, remove_tuple_expr res)
     | _ -> command
     with
     | Failure(error) -> failwith (Printf.sprintf "Error while removing tuples command %s. Error message : %s" (printCommand command) error)
    ) 
    horn.commands}


let simplify_and expr = 
let rec remove_and exp = match exp with
                           | Composition(Interpreted("and")::l) -> let flat_args = List.flatten (List.map 
                                                                                                   (fun arg -> match arg with
                                                                                                      | Interpreted("true") -> []
                                                                                                      | Composition(Interpreted("and")::q) -> q
                                                                                                      | _ -> [arg]) l) in
                                                                   if List.length flat_args > 1 then Composition(Interpreted("and")::flat_args)
                                                                   else if List.length flat_args = 1 then List.hd flat_args
                                                                   else Interpreted("true")
                           | Composition(Interpreted("=>")::Interpreted("true")::res::[]) -> res
                                                                                                     
                           | _ -> exp
                           in
  let res = exprMap remove_and expr in
  res

let simplify_or expr = 
let rec remove_or exp = match exp with
                           | Composition(Interpreted("or")::l) -> let flat_args = List.flatten (List.map 
                                                                                                   (fun arg -> match arg with
                                                                                                      | Interpreted("false") -> []
                                                                                                      | Composition(Interpreted("or")::q) -> q
                                                                                                      | _ -> [arg]) l) in
                                                                   if List.length flat_args > 1 then Composition(Interpreted("or")::flat_args)
                                                                   else if List.length flat_args = 1 then List.hd flat_args
                                                                   else Interpreted("false")                                                                        
                           | _ -> exp
                           in
  let res = exprMap remove_or expr in
  res

let msimplify expr =
  simplify_and (simplify_or expr)

let print_simplified horn =
  Printf.sprintf "%s\n"
  (printList (fun c -> match c with
             | Comment(str) -> Printf.sprintf ";%s" str
             | Unparsed(expr) -> printExpr expr
             | Fundecl(f) -> if f.return = Basic("Bool") then Printf.sprintf "(declare-fun %s (%s) Bool)" f.fname (printList printType f.params " ") else failwith "Return type of function is not bool"
             | Clause(local_var, conds, res) -> let printexp = printExpr (msimplify (func_call "=>" [(func_call "and" conds); res])) in
                                                Printf.sprintf "(assert %s)" 
                                                (if SMap.is_empty local_var then printexp 
                                                 else (Printf.sprintf "(forall (%s) %s)" (printMap (fun v -> Printf.sprintf "(%s %s)" v.vname (printType v.vtype)) local_var " ") printexp)
                                                ) 
            ) horn.commands "\n")


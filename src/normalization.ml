(*In this file, we normalize the expression, so that we only need to abstract expressions of the form new_var = abstractop(...) *)

open Types
open Helper

(*Finds an unused variable name from a list of already used names and a suggested name*)
let get_unused_var used name =
  let rec get_unused_var_numbered i =
    let tname = Printf.sprintf "%s%i" name i in
    if List.exists (fun n -> n = tname) used then (get_unused_var_numbered (i+1)) else tname in
  if List.exists (fun n -> n = name) used then (get_unused_var_numbered 0) else name

(*Normalizes an expression.
  Returns a list of new variables, a list of pair (new_var, expr) meaning new_var = expr, and the final expression without the new_var = expr*)
let rec normalize abstraction used_names expr = 
  match expr with
  | Interpreted(str) -> ([], [], expr)
  | Composition(l) -> let (tnvars, tnexprs, trexprs) = List.fold_left (fun (nvars, nexprs, rexprs) e -> 
                                                                         let (nv, ne, re) = normalize abstraction (used_names @ (List.map (fun v -> v.vname) nvars)) e in 
                                                                         (nvars @ nv, nexprs @ ne, rexprs @ [re]))
                                                                      ([], [], []) l in
                      (tnvars, tnexprs, Composition(trexprs))
  | Variable(v) -> ([], [], expr)
  | Predicate(f, l) -> let (tnvars, tnexprs, trexprs) = List.fold_left (fun (nvars, nexprs, rexprs) e -> 
                                                                         let (nv, ne, re) = normalize abstraction (used_names @ (List.map (fun v -> v.vname) nvars)) e in 
                                                                         (nvars @ nv, nexprs @ ne, rexprs @ [re]))
                                                                       ([], [], []) l in
                       (tnvars, tnexprs, Predicate(f, trexprs))
  | Extract(e1, ind) -> let (tnv1, tne1, tre1) = normalize abstraction used_names e1 in
                       (tnv1, tne1, Extract(tre1, ind))
  | TupleE(l) -> let (tnvars, tnexprs, trexprs) = List.fold_left (fun (nvars, nexprs, rexprs) e -> 
                                                                    let (nv, ne, re) = normalize abstraction (used_names @ (List.map (fun v -> v.vname) nvars)) e in 
                                                                    (nvars @ nv, nexprs @ ne, rexprs @ [re]))
                                                                    ([], [], []) l in
                 (tnvars, tnexprs, TupleE(trexprs))
  | AbstractOp(str, l) -> let (tnvars, tnexprs, trexprs) = List.fold_left (fun (nvars, nexprs, rexprs) e -> 
                                                                    let (nv, ne, re) = normalize abstraction (used_names @ (List.map (fun v -> v.vname) nvars)) e in 
                                                                    (nvars @ nv, nexprs @ ne, rexprs @ [re]))
                                                                    ([], [], []) l in
                          let abstractstr = match abstraction.operations str with
                                            | Some(f) -> f
                                            | None -> failwith (Printf.sprintf "AbstractOp type on non abstract operation : %s" str) in
                          let newvartmp = fst (abstractstr trexprs) in
                          let newvar = {vname = (get_unused_var (used_names @ (List.map (fun v -> v.vname) tnvars)) newvartmp.vname); vtype = newvartmp.vtype} in
                          (tnvars @ [newvar], tnexprs @ [(newvar, AbstractOp(str, trexprs))], Variable(newvar))


(*Normalizes the whole horn problem*)
let hornNormalize abstraction horn =
  let newcommands = List.map (fun command -> match command with
              | Clause(vars, conds, res) -> let used_names = (List.map fst (SMap.bindings vars)) @ horn.used_predicates in
                                            let (tnvars, tnexprs, trexprs) = List.fold_left (fun (nvars, nexprs, rexprs) e -> 
                                                                                               let (nv, ne, re) = normalize abstraction (used_names @ (List.map (fun v -> v.vname) nvars))  e in 
                                                                                               (nvars @ nv, nexprs @ ne, rexprs @ [re])) 
                                                                                            ([], [], []) conds in
                                            let (restnvars, restnexprs, restrexpr) = normalize abstraction (used_names @ (List.map (fun v -> v.vname) tnvars)) res in
                                            let (nvar, ne) = (tnvars @ restnvars, tnexprs @ restnexprs) in
                                            let nv = List.fold_left (fun m v -> add_unique m v.vname v) vars nvar in
                                            Clause(nv, trexprs @ (List.map (fun (v, e) -> Composition(Interpreted("=")::Variable(v)::e::[])) ne), restrexpr)
              | _ -> command) horn.commands in 
  {used_predicates = horn.used_predicates; commands = newcommands}

              
                          












                      
  

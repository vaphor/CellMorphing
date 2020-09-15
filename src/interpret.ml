(*In this file, we interpret the well parenthesized expressions : expressions starting with declare-fun and assert.*)

open Helper
open Types
                   
(*Reinterpret an expression as a type*)
let rec convert_type expr =
  match expr with
  | Interpreted(str) -> Basic(str)
  | Composition(l) -> Parametrized(List.map convert_type l)
  | _ -> failwith (Printf.sprintf "Expected a type, got %s" (printExpr expr))

(*Reinterpret an expression, taking into account variables and predicates*)
let parse_expr var_type_ctx predicate_map local_var_map expr =
  let new_var_map = ref local_var_map in
  let new_expr = exprMap 
    (fun e -> match e with
      | Interpreted(str) -> 
          if SMap.mem str local_var_map then Variable(SMap.find str local_var_map) 
          else if SMap.mem str var_type_ctx then begin new_var_map := SMap.add str (SMap.find str var_type_ctx) !new_var_map; Variable(SMap.find str var_type_ctx)  end
          else if SMap.mem str predicate_map then Predicate(SMap.find str predicate_map, []) 
          else Interpreted(str)
      | Composition(a::q) -> 
          begin match a with
          | Variable(v) -> failwith (Printf.sprintf "Variable %s as head of composition" (printExpr a));
          | Predicate(f, []) -> Predicate(f, q)
          | Interpreted("let") ->
              begin match q with
              | Composition(letlist)::exp::[] -> 
                  exprMap 
                   (fun ex -> 
                     (List.fold_left
                       (fun exp letdecl -> 
                          match letdecl with
                          | Composition(Interpreted(a)::rexp::[]) -> if exp = Interpreted(a) then rexp else exp
                          | Composition(a::b::[]) -> failwith (Printf.sprintf "Let declaration should take a variable name as first argument, given %s, in expression %s" (printExpr a) (printExpr expr))
                          | _ -> failwith (Printf.sprintf "Let declaration should take 2 arguments in expression %s" (printExpr expr))
                       )
                       ex letlist
                     )
                   ) 
                   exp
                  
              | a::b::[] -> failwith (Printf.sprintf "Let declaration should take a let declaration list as first argument, given %s, in expression %s" (printExpr a) (printExpr expr))
              | _ -> failwith (Printf.sprintf "Let declaration should take 2 arguments, given %i, in expression %s" (List.length q) (printExpr expr))
              end
          | _ -> e
          end
      | _ -> e) expr in
   (!new_var_map, new_expr)

(*Reinterprets a command taking into account asserts and declare-fun
  Returns the new map of declared predicates and the new command*)
let rec parse_command var_type_context predicate_map command =
    match command with
    | Comment(str) -> (var_type_context, predicate_map, Comment(str))
    | Unparsed(expr) -> 
        begin match expr with
        | Interpreted("assert") -> failwith (Printf.sprintf "In command %s, empty assertion" (printCommand command))
        | Interpreted("declare-fun") -> failwith (Printf.sprintf "In command %s, empty declaration" (printCommand command))
        | Interpreted(_) -> (var_type_context, predicate_map, command)
        (*A valid assertion (one parameter)*)
        | Composition(Interpreted("assert")::fc::[]) -> 
            (*We retrieve all local variables (with forall quantifier) and the rest of the clause*)
            let (local_var, clause) = match fc with 
              (*Valid forall with two parameters, the list of variable and the expression*)
              | Composition(Interpreted("forall")::vars::expr::[]) -> 
                  let lvars = match vars with
                    | Composition(lvar) when List.for_all 
                                              (fun vdecl -> match vdecl with
                                                 | Composition(Interpreted(n)::t::[]) -> true
                                                 | _ -> false
                                              ) lvar  -> lvar           
                    | _ -> failwith (Printf.sprintf "In command %s, forall requires a list of (name, type) as first parameter, got %s instead" (printCommand command) (printExpr vars))
                    in
                  (*We transform each expression as a new variable*)
                  let declared_vars = 
                    List.fold_left
                     (fun lv v ->
                        let (Composition(Interpreted(name)::vtype::[])) = v in
                        try
                          let t = convert_type vtype in
                          add_unique lv name 
                          {
                            vname = name; 
                            vtype = t
                          }
                        with
                        | Failure(error) -> failwith (Printf.sprintf "Error while converting %s as type
                                                                      in variable declaration %s
                                                                      within command %s.
                                                                      Error message : %s" (printExpr vtype) (printExpr v) (printCommand command) error)
                     ) SMap.empty lvars in
                  (declared_vars, expr)
               (*A missformed forall expression*)
               | Composition(Interpreted("forall")::q) -> failwith (Printf.sprintf "In command %s, forall declaration requires 2 parameters. Given %i." (printCommand command) (List.length q))
               | Interpreted("forall") -> failwith (Printf.sprintf "In command %s, forall requires 2 parameters. Given 0" (printCommand command))
               (*No forall declaration, the clause directly*)
               | _ -> (SMap.empty, fc)
               in
              (*Now that we have retrieved the local variables, we try to parse the clause*)
              let (nl_var, parsedclause) = try parse_expr var_type_context predicate_map local_var clause 
                                 with 
                                 | Failure(error) -> failwith (Printf.sprintf "Error while parsing the expression part %s of the clause %s. Error message : %s" 
                                                                              (printExpr clause) (printCommand command) error)
                                 in
              (*Now we try to retrieve what are conditions and what is the result*)
              let (cond, res) = 
                match parsedclause with
                | Composition(Interpreted("=>")::c::r::[]) -> 
                  begin match c with
                    | Composition(Interpreted("and")::cs) -> (cs, r)
                    | _ -> ([c], r)
                  end
                (*Ill formed "=>"*)
                | Composition(Interpreted("=>")::q) -> failwith (Printf.sprintf "In command %s, \" => \" requires two parameters, given %i" (printCommand command) (List.length q))
                | _ -> ([], parsedclause)
                in
              (var_type_context, predicate_map, Clause(nl_var, cond, res))
        | Composition(Interpreted("assert")::q) -> failwith (Printf.sprintf "In command %s, \"assert \" requires one parameter, given %i" (printCommand command) (List.length q))
        | Composition(Interpreted("rule")::clause::[]) -> 
              (*We try to parse the clause*)
              let (nl_var, parsedclause) = try parse_expr var_type_context predicate_map SMap.empty clause 
                                 with 
                                 | Failure(error) -> failwith (Printf.sprintf "Error while parsing the expression part %s of the clause %s. Error message : %s" 
                                                                              (printExpr clause) (printCommand command) error)
                                 in
              (*Now we try to retrieve what are conditions and what is the result*)
              let (cond, res) = 
                match parsedclause with
                | Composition(Interpreted("=>")::c::r::[]) -> 
                  begin match c with
                    | Composition(Interpreted("and")::cs) -> (cs, r)
                    | _ -> ([c], r)
                  end
                (*Ill formed "=>"*)
                | Composition(Interpreted("=>")::q) -> failwith (Printf.sprintf "In command %s, \" => \" requires two parameters, given %i" (printCommand command) (List.length q))
                | _ -> ([], parsedclause)
                in
              (var_type_context, predicate_map, Clause(nl_var, cond, res))
        | Composition(Interpreted("rule")::q) -> failwith (Printf.sprintf "In command %s, \"rule \" requires one parameter, given %i" (printCommand command) (List.length q))
        
        | Composition(Interpreted("declare-fun")::q) -> 
            (*A new function*)
            let f = 
              match q with
              | Interpreted(name)::Composition(params)::return::[] -> (try {fname = name; 
                                                                           params = List.map convert_type params;
                                                                           return = convert_type return}
                                                                      with
                                                                      | Failure(error) -> failwith (Printf.sprintf "Error while parsing the type of the function declaration %s. Error message : %s" 
                                                                                                    (printCommand command) error))
              | a::b::c::[] -> failwith (Printf.sprintf "In function declaration %s, a function declaration takes as parameters (name, param list, ret)" (printCommand command))
              | _ -> failwith (Printf.sprintf "In function declaration %s, a function declaration require 3 parameters (name, param list, ret). Given %i" (printCommand command) (List.length q))
              in 
             (*We require return types of functions to be bool*)
             if f.return <> Basic("Bool") then failwith (Printf.sprintf "Function declaration %s has return type different than Bool" (printCommand command)); 
             (var_type_context, add_unique predicate_map f.fname f, Fundecl(f))
        | Composition(Interpreted("declare-rel")::q) -> 
            (*A new function*)
            let f = 
              match q with
              | Interpreted(name)::Composition(params)::[] -> (try {fname = name; 
                                                                    params = List.map convert_type params;
                                                                    return = Basic("Bool")}
                                                               with
                                                               | Failure(error) -> failwith (Printf.sprintf "Error while parsing the type of the function declaration %s. Error message : %s" 
                                                                                                    (printCommand command) error))
              | a::b::c::[] -> failwith (Printf.sprintf "In function declaration %s, a relation declaration takes as parameters (name, param list)" (printCommand command))
              | _ -> failwith (Printf.sprintf "In function declaration %s, a relaton declaration require 2 parameters (name, param list). Given %i" (printCommand command) (List.length q))
              in 
             (*We require return types of functions to be bool*)
             if f.return <> Basic("Bool") then failwith (Printf.sprintf "Function declaration %s has return type different than Bool" (printCommand command)); 
             (var_type_context, add_unique predicate_map f.fname f, Fundecl(f))
        | Composition(Interpreted("declare-var")::q) -> 
              (*Global information on a variable type*)
              begin
              match q with
              (*| Interpreted("|tuple")::Composition(varlist)::Interpreted("|")::return::[] -> 
                  let vartype = (try
                                     convert_type return
                               with
                               | Failure(error) -> failwith (Printf.sprintf "Error while converting %s as type
                                                                      within command %s.
                                                                      Error message : %s" (printExpr return) (printCommand command) error)) in
                  let vlist = List.map (fun varname ->
                    match varname with
                    | Interpreted(name) -> {
                                                  vname = name; 
                                                  vtype = vartype;
                                           }
                    | _ -> failwith "In tuple variable declaration, not a variable name" ) varlist in
                  (List.fold_left (fun var_type_ctx mvar -> SMap.add mvar.vname mvar var_type_ctx) var_type_context vlist, predicate_map, Comment("Var decl"))*)
              | Interpreted(name)::return::[] -> let mvar = (try {
                                                        vname = name; 
                                                        vtype = convert_type return
                                                      }
                                   
                                                  with
                                                  | Failure(error) -> failwith (Printf.sprintf "Error while converting %s as type
                                                                      within command %s.
                                                                      Error message : %s" (printExpr return) (printCommand command) error)) in
                                                 (add_unique var_type_context mvar.vname mvar, predicate_map, Comment("Var decl"))
              | a::b::[] -> failwith (Printf.sprintf "A variable declaration must have a valid name in command %s" (printCommand command))
              | _ -> failwith (Printf.sprintf "In variable declaration %s, a variable declaration require 2 parameters (name, ret). Given %i" (printCommand command) (List.length q))
              end
             
        | Composition(Interpreted("query")::query::[]) -> parse_command var_type_context predicate_map (Unparsed(Composition(Interpreted("rule")::Composition(Interpreted("=>")::query::Interpreted("false")::[])::[])))
        | _ -> (var_type_context, predicate_map, command)
        end
    | _ -> (var_type_context, predicate_map, command)

(*Converts a horn problem*)
let convert_horn horn=
  let (declvars, predicates, converted) = 
    List.fold_left (fun (v_type_ctx, pmap, conv) c -> let (nv_type_ctx, npmap, nc) = parse_command v_type_ctx pmap c in
                                          (nv_type_ctx, npmap, conv @ [nc])) 
                   (SMap.empty, SMap.empty, [])
                   horn.commands in
  {used_predicates = getKeys predicates; commands = converted}




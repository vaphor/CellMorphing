(*In this file, we apply the type abstraction and we recognize the abstract operation (without doing anything to them yet). *)

open Types
open Helper

(*We apply alpha(abstraction) and we interpret abstract operations (but we do not do anything with them)*)
let rec transform abstraction command =
  match command with
  | Comment(str) -> command
  | Unparsed(expr) -> command
  | Fundecl(f) ->
      (*We transform types of function declarations*) 
      if f.return <> Basic("Bool") then failwith (Printf.sprintf "Predicate with return type different from Bool : %s" (printType f.return));
      Fundecl({fname = f.fname; params = List.map (fun t -> fst (abstraction.types t)) f.params; return = f.return})
  | Clause(lv, conds, res) -> let (newvars, inits) = 
                                (*We transform the local vars*)
                                SMap.fold (fun name v (nlv, initexprs) -> 
                                                 let abstract = abstraction.types v.vtype in
                                                 let nv = {vname = v.vname; vtype = fst abstract} in
                                                 let ne = (snd abstract) (Variable(nv)) in
                                                 (SMap.add name nv nlv, initexprs @ [ne])
                                               ) lv (SMap.empty, []) in
                               (*We change the variables and operations within the expression*)
                               let mreplace = exprMap (fun e -> match e with
                                              | Variable(v) -> Variable({vname = v.vname; vtype = fst (abstraction.types v.vtype)})
                                              | Composition(Interpreted(str)::q) -> begin match abstraction.operations str with
                                                                                    | Some(f) -> AbstractOp(str, q)
                                                                                    | _ -> e
                                                                                    end
                                              | _ -> e) in
                               Clause(newvars, inits @ (List.map mreplace conds), mreplace res)
                                               

(*Transforms the whole horn problem*)
let transformHorn abstraction horn =
  {used_predicates = horn.used_predicates; commands = List.map (transform abstraction) horn.commands}


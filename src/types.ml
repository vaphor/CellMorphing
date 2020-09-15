open Helper

(*An expression is used to represent anything.
  Some expressions have a meaning and have a special constructors such as Variable, Predicate, ...
  and others such as Interpreted and Composition just mean a well parethesised expression in prefix notation*)
type expr =
| Interpreted of string (*A string that we assume z3 knows how to interpret*)
| Composition of expr list (*A list or function application that we assume z3 already knows how to interpret*)
| Variable of var (*A variable*)
| Predicate of func * (expr list) (*A predicate, that is to say something declared with declare-fun. An \exists semantic*)
| TupleE of expr list (*A tuple expression (z3 does not deal with those yet...)*)
| Extract of expr * int (*Operation consisting in retrieving a part of a tuple expression*)
| AbstractOp of string * expr list (*An abstract operation that we need to transform*)

(*The only type we really interpret is the Tuple type*)
and v_type =
| Basic of string (*A simple type*)
| Parametrized of v_type list (*A type taking type parameters*)
| TupleT of (v_type * (string option (*suffix*))) list (*A tuple type. The string option is a hack to have decent names when we expand a tuple variable into several variables. 
                                                         If present Extract(var, i) has as variable name var.vname_suffix.
                                                         Otherwise : var.vname_i*)

(*A variable is a name and a type*)
and var =
{
  vname : string;
  vtype : v_type
}

(*Function type, though we only deal with predicates*)
and func =
{
  fname : string;
  params : v_type list; (*param type*)
  return : v_type; (*return type*)
}

(*A command is an instruction given to z3*)
type command =
| Comment of string (*A comment*)
| Unparsed of expr (*Some command we do not try to understand, such as set-logic, check-sat, ...*)
| Fundecl of func (*Declaration of a function : declare-fun*)
| Clause of (var SMap.t) * (expr list) * expr (*A horn clause : assert (forall vars, cond1 /\ cond2 /\ ... => res*)

(*The complete horn problem*)
type horn =
{
  used_predicates : string list; (*declared funs*)
  commands : command list (*commands*)
}

(*An abstration definition*)
type abstraction =
{
  (*The abstraction function \alpha*)
  types : v_type (*Concrete type*)-> 
           (v_type (*Abstract type, can be the same as the concrete type*) * 
           (*conditions for subtyping : usefull to have ordered(Z^2) instead of Z^2 for example. We just add the condition i1 < i2*)
           (expr (*An expression containing the variable we abstract (already abstracted). For example Variable({vname = tab; vtype = TupleT(Basic("Int"), Basic("Int"))})*)
             -> expr)) (*The condition Extract(tab, 0) < Extract(tab,1) for example*);

  (*The abstraction for operations such as select, store, ...
    Here, we assume that types have already been abstracted.
    Furthermore, we will only need to abstract expressions of the form new_variable = abstract_op(params)*)
  operations : string (*operation name*)-> 
                         (*The optional abstraction of the operation. Return None for no abstraction.*)
                         ((
                         expr list (*Parameters for the abstraction.*)-> 
                           (var (*The suggested variable we should create for the result of abstract_op(params). 
                                  Note that the type of that variable is required for the program to work, 
                                  but the variable name is just to help make the result readable*) * 
                           (var (*The actual variable chosen for the new_variable. It will have same type as the suggested variable 
                                   but might have a different name due to name collision*)-> 
                            expr list (*Context containing all other non abstracted conditions. 
                                        This is mostly used for operations such as select who require predicate modifications*)-> 
                              expr) (*A list of expressions abstracting the operation. 
                                           The new clause becomes a list of clause formed by the clause in which the operation new_variable = abstract_op(params)
                                           is replaced by one of the expression list.
                                           For example tmp = store(tab, 1,2) will return
                                           Extract(tmp, index) = Extract(tab, index) /\ 1 != Extract(tab, index) /\ Extract(tmp, value) = Extract(tab, value)
                                           Extract(tmp, index) = Extract(tab, index) /\ 1 = Extract(tab, index) /\ Extract(tmp, value) = 2*)
                                            )) option )
}





(*Type printer in smt2 format, (except when tuples are defined)*)
let rec printType t =
  match t with
  | Basic(str) -> Printf.sprintf "%s" str
  | Parametrized(types) -> Printf.sprintf "(%s)" (printList printType types " ")
  | TupleT(vtypelist) -> Printf.sprintf "(tuple %s)" (printList printType (List.map fst vtypelist) " ")


(*Expression printer in smt2 format (except for tuples)*)
let rec printExpr expr =
  match expr with
  | Interpreted(str) -> Printf.sprintf "%s" str
  | Composition(exprs) -> if List.length exprs = 1 then
                          begin
                            if List.hd exprs = Interpreted("and") then Printf.sprintf "true"
                            else
                            begin
                             (*Printf.printf "Warning : no arguments for composition with head %s...\n" (printExpr (List.hd exprs));*)
                             Printf.sprintf "(%s)" (printList printExpr exprs " ")
                            end
                         end
                         else
                           Printf.sprintf "(%s)" (printList printExpr exprs " ")
  | Variable(v) -> Printf.sprintf "%s" v.vname
  | Predicate(f, params) -> if (List.length params) =0 then f.fname else Printf.sprintf "(%s %s)" f.fname (printList printExpr params " ")
  | Extract(e, index) -> Printf.sprintf "(extract %s %i)" (printExpr e) (index)
  | TupleE(le) -> Printf.sprintf "(tuple %s)" (printList printExpr le " ")
  | AbstractOp(str, l) -> Printf.sprintf "(AbstractOp : %s %s)" str (printList printExpr l " ")

let printCommand c =
  match c with
  | Comment(str) -> Printf.sprintf ";%s" str
  | Unparsed(expr) -> printExpr expr
  | Fundecl(f) -> Printf.sprintf "(declare-fun %s (%s) %s)" f.fname (printList printType f.params " ") (printType f.return)
  | Clause(local_var, conds, res) -> Printf.sprintf "(assert (forall (%s) (=> (and %s) %s)))" (printMap (fun v -> Printf.sprintf "(%s %s)" v.vname (printType v.vtype)) local_var " ") 
                                                                                              (printList printExpr conds " ")
                                                                                              (printExpr res)

(*Horn problem printer in smt2 format*)
let printHorn horn =
  printList printCommand horn.commands "\n"

(*Type deducing mechanism for expressions*)
let rec deduceType e =
  match e with
    | Interpreted(str) ->failwith (Printf.sprintf "Unable to deduce type of expression : %s" (printExpr e))
    | Composition(l) -> begin match l with
                        | [] -> failwith (Printf.sprintf "Unable to deduce type of expression : %s" (printExpr e))
                        | Interpreted("and")::q -> Basic("Bool")
                        | Interpreted("or")::q -> Basic("Bool")
                        | Interpreted("not")::q -> Basic("Bool")
                        | Interpreted(">")::q -> Basic("Bool")
                        | Interpreted("<")::q -> Basic("Bool")
                        | Interpreted(">=")::q -> Basic("Bool")
                        | Interpreted("<=")::q -> Basic("Bool")
                        | Interpreted("=")::q -> Basic("Bool")
                        | _ -> failwith (Printf.sprintf "Unable to deduce type of expression : %s" (printExpr e))
                        end
    | Variable(v) -> v.vtype
    | Predicate(f, l) -> Basic("Bool")
    | Extract(expr, i) -> begin match deduceType expr with
                          | TupleT(l) -> (List.nth (List.map fst l) i)
                          | _ -> failwith (Printf.sprintf "Extract on non tuple expression : %s" (printExpr e))
                          end
    | TupleE(l) -> TupleT(List.map (fun e -> (deduceType e, None)) l)
    | AbstractOp(str,l) -> failwith (Printf.sprintf "Can not deduce the type of an abstract operation. In our case : %s" (printExpr e))

(*Quick notation for the expression defined by a function call*)
let func_call str l =
  match str with
  | "!=" -> Composition(Interpreted("not")::Composition(Interpreted("=")::l)::[])
  | _ -> Composition(Interpreted(str)::l)

(*Quick notation for the and expression*)
let andExpr l =
  func_call "and" l

(*Applies recursively f to the expression from the inside of the expression to the outside. Does not reapply f on the expression generated by f*)
let rec exprMap f expr =
  match expr with
  | Interpreted(str) -> f expr
  | Composition(l) -> f (Composition (List.map (exprMap f) l))
  | Variable(v) -> f expr
  | Predicate(p, l) -> f (Predicate (p, List.map (exprMap f) l))
  | Extract(e, i) -> f (Extract (exprMap f e, i)) (*get ith element of a tuple, starts at index 0*)
  | TupleE(l) -> f (TupleE (List.map (exprMap f) l))
  | AbstractOp(str, l) -> f (AbstractOp (str, List.map (exprMap f) l))

(*Does not change anything for operations that do not take a list in their parameters. 
  For those that do, returns Op(f(param1) @ f(param2) ... f(paramn))
  Should be used with exprMap to flatten expr (such as ands, tuples, ...) *)
let exprLinearlize f expr =
  match expr with
  | Composition(l) -> Composition (List.flatten (List.map f l))
  | Predicate(p, l) -> Predicate (p, List.flatten (List.map f l))
  | TupleE(l) -> TupleE (List.flatten (List.map f l))
  | AbstractOp(str, l) -> AbstractOp (str, List.flatten (List.map f l))
  | _ -> expr

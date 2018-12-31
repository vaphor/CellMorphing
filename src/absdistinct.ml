(*This file is part of Vaphor

    Vaphor is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Vaphor is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Vaphor.  If not, see <https://www.gnu.org/licenses/>. *)


(*In this file, we give the abstraction of SAS2016 and we abstract the operations*)

open Types
open Helper

(*Returns the abstraction of SAS2016 on arrays with distinct number = n.
  To better andurstand what is happening, you should read the part on the abstraction type in types.ml*)
let absdistinct n = 
  (*Alpha (type abstraction) : Array(Int, V) -> (Int x V) ^ n such that the integers are ordered
                               _ -> the same thing*)
  let rec abstract_type concrete =
      match concrete with
      | Parametrized(Basic("Array")::q) ->
              (*Abstracting Array*) 
              begin match q with
                | a::b::[] -> (*We only deal with arrays of integers*)
                              if a <> Basic("Int") then failwith (Printf.sprintf "Warning : non integer indexed Array. Type is %s " (printType concrete));
                              (*The abstraction is recursive, therefore we abstract the value type*) 
                              let value_type = fst (abstract_type b) in
                              (*Each distinct is a pair of Int, Value*)
                              let distinct_type = TupleT((*index*)(Basic("Int"), Some("ind"))::(*value*)(value_type, Some("val"))::[]) in
                              (*We create n of such pairs*)
                              let tuple_type = TupleT(listCreate (fun s -> (distinct_type, None)) n) in
                              (*We add the conditions i0 < i1 < ... < i(n-1)*)
                              (tuple_type, fun tab -> andExpr (listCreate (fun i -> (*index_i < index_(i+1)*)
                                                                                    let distinct_expr = tab in
                                                                                    let f_expr = Extract(distinct_expr, i) in
                                                                                    let s_expr = Extract(distinct_expr, i+1) in
                                                                                    let fi_expr = Extract(f_expr,0) in
                                                                                    let si_expr = Extract(s_expr,0) in
                                                                                    func_call "<" [fi_expr; si_expr]) (n-1))
                             )
                | _ -> failwith (Printf.sprintf "Array type must have two arguments. Given %s" (printType concrete))
              end
      (*Other types have same type as abstraction*)
      | _ -> (concrete, fun t -> andExpr []) in

    (*We abstract operations select and store. 
      store just modifies all values where the index coincides and keeps the other values identical
      select returns the value given by one of the distinct if the index coincides and otherwise tries to finds an other instance where the index coincides*)
    let operations str =
      match str with
      | "store" -> let replace_func params =
                     match params with
                     | tab::index::value::[] -> 
                       let printedTab = printExpr tab in
                       (*Suggested variable. Type is type of tab and suggested name is tmp_store_tabname*)
                       let suggested_var = {vname = Printf.sprintf "tmp_store_%s" (firstWord printedTab); vtype = deduceType tab} in
                       (*Description of how to abstract the operation*)
                       let abstract_op created_var predicates =
                         let new_var = Variable(created_var) in
                         let general_condition = 
                             (*index of the new var is equal to the index of the old var*)
                             andExpr (listCreate (fun i -> func_call "=" [Extract(Extract(new_var, i), 0); 
                                                                          Extract(Extract(tab, i), 0)]) n) in
                         
                         (*list of expression saying new_distinct_i_val = old_distinct_i_val*)
                         let valEquals = listCreate (fun i -> func_call "=" [Extract(Extract(new_var, i), 1); 
                                                                             Extract(Extract(tab, i), 1)]) n in

                         let matchedcases = listCreate (fun i ->
                           andExpr
                           [
                             (*index = distinct_i*)
                             func_call "="  [Extract(Extract(tab, i), 0); index];
                             (*All new values are equal to old values but for distinct_i*)
                             andExpr (listRemove valEquals i);
                             (*val_distinct_i = value*)
                             func_call "="  [Extract(Extract(new_var, i), 1); value]
                           ]) n in

                         let unmatchedcase =
                           [
                             andExpr
                             [
                             (*distinct_i <> index*)
                             andExpr (listCreate (fun i -> func_call "!="  [Extract(Extract(tab, i), 0); index]) n);
                             (*All new values are equal to old values*)
                             andExpr valEquals
                             ]
                           ] in
                           
                         andExpr([general_condition; func_call "or" (matchedcases @ unmatchedcase)]) in
                         (suggested_var, abstract_op)
                     | _ -> failwith (Printf.sprintf "store requires three parameters. Given %s" (printList (fun e -> Printf.sprintf "(%s : %s)" (printExpr e) (printType (deduceType e))) params " "))
                     in
                     Some(replace_func)
      | "insert" -> let replace_func params =
                     match params with
                     | tab::index::value::[] -> 
                       let printedTab = printExpr tab in
                       (*Suggested variable. Type is type of tab and suggested name is tmp_store_tabname*)
                       let suggested_var = {vname = Printf.sprintf "tmp_insert_%s" (firstWord printedTab); vtype = deduceType tab} in
                       (*Description of how to abstract the operation*)
                       let abstract_op created_var predicates =
                         let new_var = Variable(created_var) in
                         
                         
                         let res = func_call "or"
                         [
                           func_call "or" (listCreate 
                           (fun i ->
                             (*case res_index_i = index*)
                             andExpr 
                             [
                               (*res_index_i = index and res_value_i = value*)
                               andExpr 
                               [
                                 (func_call "=" [Extract(Extract(new_var, i), 0); index]); 
                                 (func_call "=" [Extract(Extract(new_var, i), 1); value])
                               ];
                               (*res_index_j when j < i, res_index_j = tab_index_j and res_value_j = tab_value_j*)
                               andExpr (listCreate 
                               (fun j ->
                                 andExpr 
                                 [
                                   func_call "=" [Extract(Extract(new_var, j), 0); Extract(Extract(tab, j), 0)];
                                   func_call "=" [Extract(Extract(new_var, j), 1); Extract(Extract(tab, j), 1)]
                                 ]
                               ) i);
                               (*res_index_j when j > i, res_index_j = tab_index_j+1 and res_value_j = tab_value_j*)
                               andExpr (listCreate 
                               (fun k ->
                                 let j = k + i +1 in
                                 andExpr 
                                 [
                                   func_call "=" [Extract(Extract(new_var, j), 0); (func_call "+" [Extract(Extract(tab, j), 0); Interpreted("1")])];
                                   func_call "=" [Extract(Extract(new_var, j), 1); Extract(Extract(tab, j), 1)]
                                 ]
                               ) (n-i-1))
                             ]
                           ) n);
                           func_call "or" (listCreate 
                           (fun i ->
                             (*case res_index_i < index < res_index_i+1*)
                             andExpr 
                             [
                               (*res_index_i < index < res_index_i+1*)
                               andExpr 
                               [
                                 (func_call "<" [Extract(Extract(new_var, i), 0); index]); 
                                 (func_call "<" [index; Extract(Extract(new_var, i+1), 0)])
                               ];
                               (*res_index_j when j <= i, res_index_j = tab_index_j and res_value_j = tab_value_j*)
                               andExpr (listCreate 
                               (fun j ->
                                 andExpr 
                                 [
                                   func_call "=" [Extract(Extract(new_var, j), 0); Extract(Extract(tab, j), 0)];
                                   func_call "=" [Extract(Extract(new_var, j), 1); Extract(Extract(tab, j), 1)]
                                 ]
                               ) (i+1));
                               (*res_index_j when j > i, res_index_j = tab_index_j+1 and res_value_j = tab_value_j*)
                               andExpr (listCreate 
                               (fun k ->
                                 let j = k + i +1 in
                                 andExpr 
                                 [
                                   func_call "=" [Extract(Extract(new_var, j), 0); (func_call "+" [Extract(Extract(tab, j), 0); Interpreted("1")])];
                                   func_call "=" [Extract(Extract(new_var, j), 1); Extract(Extract(tab, j), 1)]
                                 ]
                               ) (n-i-1))
                             ]
                           ) (n-1));
                           func_call "or"
                             [
                               (*index < res_index_0*)
                               func_call "<" [index; Extract(Extract(new_var, 0), 0)];
                               (*res_index_j = tab_index_j+1 and res_value_j = tab_value_j*)
                               andExpr (listCreate 
                               (fun j ->
                                 andExpr 
                                 [
                                   func_call "=" [Extract(Extract(new_var, j), 0); (func_call "+" [Extract(Extract(tab, j), 0); Interpreted("1")])];
                                   func_call "=" [Extract(Extract(new_var, j), 1); Extract(Extract(tab, j), 1)]
                                 ]
                               ) n)
                             ];
                           func_call "or" 
                             [
                               (*res_index_(n-1) < index*)
                               func_call "<" [Extract(Extract(new_var, n-1), 0); index];
                               (*res_index_j = tab_index_j and res_value_j = tab_value_j*)
                               andExpr (listCreate 
                               (fun j ->
                                 andExpr 
                                 [
                                   func_call "=" [Extract(Extract(new_var, j), 0); Extract(Extract(tab, j), 0)];
                                   func_call "=" [Extract(Extract(new_var, j), 1); Extract(Extract(tab, j), 1)]
                                 ]
                               ) n);
                             ]
                         ] in
                         
                         res in
                         (suggested_var, abstract_op)
                     | _ -> failwith (Printf.sprintf "store requires three parameters. Given %s" (printList (fun e -> Printf.sprintf "(%s : %s)" (printExpr e) (printType (deduceType e))) params " "))
                     in
                     Some(replace_func)


      | "select" -> let replace_func params =
                     match params with
                     | tab::index::[] ->
                       let printedTab = printExpr tab in
                       (*Suggested variable. Type is value type of tab and suggested name is tmp_select_tabname*)
                       let suggested_var = {vname = Printf.sprintf "tmp_select_%s" (firstWord printedTab); vtype = match deduceType tab with
                                                                                                                   |TupleT((TupleT([(Basic("Int"), _); (value_type, _)]), _)::q) -> value_type 
                                                                                                                   | _ -> failwith "Can not deduce value type in select" } in
                       (*Description of how to abstract the operation*)
                       let abstract_op created_var predicates =
                         let new_var = Variable(created_var) in

                         let matchedcases = listCreate (fun i ->
                           andExpr
                           [
                             (*index = distinct_i*)
                             func_call "="  [Extract(Extract(tab, i), 0); index];
                             (*new_var = value_i*)
                             func_call "="  [new_var; Extract(Extract(tab, i), 1)];
                           ]) n in
                         
                         (*Let us consider that index is added to the order i0 < i1 ... <i(n-1) giving i0 < i1 <... < index < ... < i(n-1)
                           This returns that order where index is in position insert_pos and i_del is removed
                           Furthermore, we inject that in the current predicates.
                           For example, if the predicate is P(tab = ((i0, v0), i1, v1)) insert_pos = 1 and del = 1, we get P((i0, v0), (index, new_var))
                                        if the predicate is P(tab = ((i0, v0), i1, v1)) insert_pos = 0 and del = 1, we get P((index, new_var), (i0, v0))
                         *)

                         let fpredicates insert_pos del = List.flatten (List.map (fun cond -> 
                          let tmp = exprMap 
                           (fun e -> match e with
                              | t when t = tab -> 
                                    let basicArgList = listCreate (fun i -> Extract(tab, i)) n in
                                    let deletedArgList = listRemove basicArgList del in
                                    let newinsert_pos = (if insert_pos > del then insert_pos-1 else insert_pos) in
                                    let finalList = listInsert deletedArgList (TupleE([index; new_var])) newinsert_pos in
                                    TupleE(finalList)  
                              | _ -> e
                           ) cond in
                          if cond = Composition(Interpreted("=")::new_var::AbstractOp("select", params)::[]) then []
                          else if tmp = cond then [] else [tmp]) predicates) in

                         let unmatchedcases = 
                            (*case : index < distinct_0*)
                            [andExpr
                             [
                             func_call "<"  [index; Extract(Extract(tab, 0), 0)];
                             (*Predicates with index, new_var*)
                             andExpr (listCreate (fun del -> andExpr (fpredicates 0 del)) n)
                             ]]
                           @
               
                           (listCreate (fun i -> 
                             andExpr
                             [
                             (*case : distinct_(i) < index < distinct_i+1*)
                             andExpr [func_call "<"  [Extract(Extract(tab, i), 0); index]; func_call "<"  [index ; Extract(Extract(tab, i+1), 0)]];
                             (*Predicates with index, new_var*)
                             andExpr (listCreate (fun del -> andExpr (fpredicates (i+1) del)) n)
                             ]
                            )
                            (n-1))

                            @
                            (*case : distinct_(n-1) < index*)
                            [andExpr
                             [
                             func_call "<"  [Extract(Extract(tab, n-1), 0); index];
                             (*Predicates with index, new_var*)
                             andExpr (listCreate (fun del -> andExpr (fpredicates n del)) n)
                             ]]
                            
                            
                      in
                         func_call "or" (matchedcases @ unmatchedcases) in
                         (suggested_var, abstract_op)
                     | _ -> failwith (Printf.sprintf "select requires two parameters. Given %s" (printList (fun e -> Printf.sprintf "(%s : %s)" (printExpr e) (printType (deduceType e))) params " "))
                     in
                     Some(replace_func)                             
      | _ -> (None) in
  {types = abstract_type; operations = operations}


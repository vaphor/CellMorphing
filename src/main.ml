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


(*
In this file, we give the main function of the program.
The goal of the program is to convert a horn problem in smt2 format 
into a horn problem in smt2 format with given types are abstracted.

To define a new abstraction, one needs to create an abstraction type (as defined in types.ml).

Once an abstraction is given, the program follows the following steps.

1) It parses the input file without understanding it : it only retrieves the well parenthesized expression
   This is done in horn_lexer.mll and horn_parser.mly.

2) We interpret the well parenthesized expressions : expressions starting with declare-fun and assert.
   This is done in interpret.ml

3) We apply the type abstraction and we recognize the abstract operation (without doing anything to them yet).
   This is done in transform.ml

4) We normalize the expression, so that we only need to abstract expressions of the form new_var = abstractop(...)
   This is done in normalization.ml

5) We finally abstract the operations.
   this is done in abstraction.ml

6) We simplify the expressions (get rid of tuples, ...)
   This is done in simplification.ml
*)




open Format
open Printexc
open Filename
open Types
open Helper
open Normalization
open Abstraction
open Simplification
open Config
open Transform
open Interpret



let parse config =
  (*Checking Existence of input file*)
  if String.compare config.f_name "" = 0 then failwith ("No input file. Filename read is \""^config.f_name^"\"");
  Localizing.current_file_name := config.f_name;

  (*Opening file*)
  let f_desc = try open_in config.f_name 
  with 
    | Sys_error(e) -> failwith ("Impossible to open file. Filename read is \""^config.f_name^"\"") in

  (* Lexing *)
  let lexbuf = Lexing.from_channel f_desc in
  let horn_problem = 
    (*Parsing*)
    try Horn_parser.horn Horn_lexer.token lexbuf
    (*Retrieving where the error is*)
    with exn ->
      begin
        let curr = lexbuf.Lexing.lex_curr_p in
        let line = curr.Lexing.pos_lnum in
        let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
        let tok = Lexing.lexeme lexbuf in
        let tail = Horn_lexer.ruleTail "" lexbuf in
        failwith (Printf.sprintf "Problem when parsing (probably due to characters just before) %s %i %i" (tok^tail) cnum line )  (*raise (Error (exn,(line,cnum,tok)))*)
      end in
   horn_problem


let _  =
  (*Show where exceptions comme from*)
  Printexc.record_backtrace(true);

  try
    (*Read arguments*)
    let cf = read_args() in

    (*Only show where expressions come from and show filename when debug is activated*)
    Printexc.record_backtrace(cf.debug);
    if cf.debug then Printf.printf "File is %s\n" cf.f_name;

    (*Retrieving program in as expressions. Nothing is interpreted yet*)
    let horn = parse cf in
    if cf.debug then Printf.printf "Printing parsed expression :\n%s\n\n\n" (printHorn horn);

    (*We interpret variables, asserts, function declarations, foralls, ...*)
    let converted = convert_horn horn in
    if cf.debug then Printf.printf "Printing converted expression :\n%s\n\n\n" (printHorn converted);
    

    (*Abstraction we use*)
    let mabstraction = absdistinctsize (cf.distinct_i) in

    (*We now retrieve the abstract operations and we apply alpha (the abstraction for types) *)
    let transformed = (transformHorn mabstraction converted) in
    if cf.debug then Printf.printf "Printing transformed expression :\n%s\n\n\n" (printHorn transformed);
    
    (*Now that we know the abstract operations, we can normalize the expression*)
    let normalized = hornNormalize mabstraction transformed in
    if cf.debug then Printf.printf "Printing normalized expression :\n%s\n\n\n" (printHorn normalized);
    
    (*We now abstract the operations*)
    let abstracted = abstractHorn mabstraction normalized in
    if cf.debug then Printf.printf "Printing abstracted expression :\n%s\n\n\n" (printHorn abstracted);

    (*We finally simplify the expression (consists in removing the tuples)*)
    let final = remove_tuples abstracted in
    if cf.debug then Printf.printf "Printing tuple removed expression :\n%s\n\n\n" (printHorn final);
    
    (*Getting simplified horn string*)
    let str_final = (print_simplified final) in
    if cf.debug then Printf.printf "Printing final expression :\n%s\n\n\n" str_final;

    let outfile = open_out cf.outputsmt_name in
    Printf.fprintf outfile "%s" str_final;
  with
    (*Whenever an exception is thrown, print expression and backtrace (empty if debug = false), and exit with -1 status*)
    | e -> Printf.printf "\n\nException : %s %s\n\n" (Printexc.to_string e) (Printexc.get_backtrace ()); exit (-1)





%{


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
    
open Helper
open Types

(*Everything is an expression at this point. We will reinterpret types, foralls, asserts, ... later on*)
%}

%token LBRACE RBRACE EOF
%token <string> WORD COMMENT

%start horn
%type <expr list> expression_list
%type <expr> expression
%type <Types.command list> commands
%type <Types.horn> horn
%%

expression_list:
| {[]}
| expression expression_list {$1::$2}

expression:
| WORD {Interpreted($1)}
| LBRACE expression_list RBRACE {Composition($2)}

commands:
| EOF {[]}
| COMMENT commands {(Comment($1))::$2} 
| expression commands {(Unparsed($1))::$2}

horn:
| commands {{used_predicates = []; commands = $1}}




%{
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



%{
open Ast
%}

%token TRUE
%token FALSE
%token NOT
%token AND
%token OR
%token PLUS
%token MINUS
%token MUL
%token EQ
%token NEQ
%token LEQ
%token LE
%token GEQ
%token GE
%token <string> ID
%token <string> CONST
%token <string> STRING
%token <string> ADDRLIT

%token SKIP
%token TAKES
%token CMDSEP
%token IF
%token ELSE
%token REQ

%token LPAREN
%token RPAREN
%token LBRACE
%token RBRACE
%token EOF

%token CONTRACT
%token CONSTR
%token FUN
%token INT
%token BOOL
%token ADDR
%token FIELDSEP
%token THIS
%token MSGSENDER
%token BALANCE
%token TRANSFER
%token TOKSEP
%token ARGSEP
%token PUBLIC
%token PRIVATE

%token FAUCET
%token DEPLOY

%left OR
%left AND
%nonassoc NOT
%left EQ LEQ
%left PLUS MINUS
%left MUL

%left CMDSEP (* bart: check *)
%nonassoc ELSE

%start <contract> contract
%type <exprval> value
%type <var_decl> var_decl
%type <modifier> modifier
%type <fun_decl> fun_decl
%type <cmd> cmd
%type <var_decls> formal_args
%type <expr> expr 

%start <cmd> cmd_test

%start <transaction> transaction
%start <cli_cmd> cli_cmd

%%

contract:
  | CONTRACT; c=ID; LBRACE; vdl = list(var_decl); fdl = list(fun_decl); RBRACE; EOF { Contract(c,vdl,fdl) }
;

actual_args:
  | a = separated_list(ARGSEP, value) { a } ;

value:
  | n = CONST { Int (int_of_string n) }
  | s = STRING { Addr s }
  | TRUE { Bool true }
  | FALSE { Bool false }

expr:
  | n = CONST { IntConst(int_of_string n) }
  | s = STRING { AddrConst(s) }
  | THIS { This }
  | MSGSENDER { Var("msg.sender") }
  | e=expr; FIELDSEP; BALANCE { BalanceOf(e) }
  | TRUE { True }
  | FALSE { False }
  | NOT; e=expr { Not e }
  | e1=expr; AND; e2=expr { And(e1,e2) }
  | e1=expr; OR; e2=expr { Or(e1,e2) }
  | e1=expr; PLUS; e2=expr { Add(e1,e2) }
  | e1=expr; MINUS; e2=expr { Sub(e1,e2) }
  | e1=expr; MUL; e2=expr { Mul(e1,e2) }
  | e1=expr; EQ; e2=expr { Eq(e1,e2) }
  | e1=expr; NEQ; e2=expr { Neq(e1,e2) }
  | e1=expr; LEQ; e2=expr { Leq(e1,e2) }
  | e1=expr; LE; e2=expr { Le(e1,e2) }
  | e1=expr; GEQ; e2=expr { Geq(e1,e2) }
  | e1=expr; GE; e2=expr { Ge(e1,e2) }
  | x = ID { Var(x) }
  | LPAREN; e = expr; RPAREN { e }
;

nonseq_cmd:
  | SKIP; CMDSEP;  { Skip }
  | REQ; e = expr; CMDSEP; { Req(e) } 
  | x = ID; TAKES; e = expr; CMDSEP; { Assign(x,e) }
  | rcv=expr; FIELDSEP; TRANSFER; LPAREN; amt=expr; RPAREN; CMDSEP; { Send(rcv,amt) }
  | f = ID; LPAREN; el = separated_list(ARGSEP, expr) RPAREN; CMDSEP; { Call(f,el) }

cmd:
  | c = nonseq_cmd { c }
  | c1 = cmd; c2 = cmd { Seq(c1,c2) }
  | IF LPAREN; e = expr; RPAREN; c1 = nonseq_cmd ELSE c2 = nonseq_cmd { If(e,c1,c2) }
  | IF LPAREN; e = expr; RPAREN; LBRACE; c1 = cmd; RBRACE; ELSE c2 = nonseq_cmd { If(e,c1,c2) }
  | IF LPAREN; e = expr; RPAREN; c1 = nonseq_cmd; ELSE LBRACE; c2 = cmd; RBRACE; { If(e,c1,c2) }
  | IF LPAREN; e = expr; RPAREN; LBRACE; c1 = cmd; RBRACE; ELSE; LBRACE; c2 = cmd; RBRACE { If(e,c1,c2) }
  | LBRACE; c = cmd; RBRACE { c }
  | LBRACE; vdl = list(var_decl) c = cmd; RBRACE { Block(vdl, c) }
;

var_decl:
  | INT x = ID; CMDSEP { IntVar x }
  | BOOL x = ID; CMDSEP { BoolVar x }
  | ADDR x = ID; CMDSEP { AddrVar x }
;

modifier:
  | PUBLIC { Public }
  | PRIVATE { Private }
;

fun_decl:
  | CONSTR; LPAREN; al = formal_args; RPAREN; LBRACE; c = cmd; RBRACE { Proc("constructor",al,c,Public) }
  | FUN; f = ID; LPAREN; al = formal_args; RPAREN; m=modifier; LBRACE; c = cmd; RBRACE { Proc(f,al,c,m) }
  | FUN; f = ID; LPAREN; al = formal_args; RPAREN; m=modifier; LBRACE; RBRACE { Proc(f,al,Skip,m) }
;

cmd_test:
  | c = cmd; EOF { c }
;

formal_args:
  | a = separated_list(ARGSEP, formal_arg) { a } ;

formal_arg:
  | INT; x = ID { IntVar x }
  | BOOL; x = ID { BoolVar x }
  | ADDR; x = ID { AddrVar x }
;

transaction:
  | sender = ADDRLIT; TOKSEP; contr = ADDRLIT; FIELDSEP; f = ID; LPAREN; al = actual_args; RPAREN { Tx(sender,contr,f,al) } 
;

cli_cmd:
  | tx = transaction { ExecTx tx }
  | FAUCET; a = ADDRLIT; n = CONST { Faucet(a, int_of_string n) }
  | DEPLOY; a = ADDRLIT; filename = STRING { Deploy(a,filename) }
;
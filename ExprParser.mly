%{open Syntax
%}

%token <int> INT
%token <string> ID
%token <bool> BOOL
%token IF THEN ELSE
%token LET IN
%token FUN REC AND
%token MATCH WITH BAR END
%token ARROW
%token PLUS
%token MINUS
%token MUL
%token DIV
%token EQ
%token LE
%token LPAR RPAR
%token COMMA
%token NIL DCOLON
%token COMEND
%token EOF

%start main
%type <Syntax.command> main
%%

main:
 |LET ID EQ expr COMEND {Let (VString $2, $4)}
 |LET REC ID ID EQ expr COMEND {LetRec (VString $3, VString $4, $6)}
 |LET REC lr COMEND {LetRecAnd $3}
 |expr COMEND {CExp $1}
 |expr EOF {CExp $1}
;

expr:
 |FUN ID ARROW expr {EFun (VString $2, $4)}
 |LET ID EQ expr IN expr {LetIn (VString $2, $4, $6)}
 |LET REC ID ID EQ expr IN expr {ERecIn (VString $3, VString $4, $6, $8)}
 |LET REC lr IN expr {ERecAndIn ($3, $5)}
 |MATCH expr WITH pattern ARROW expr pats {EMatch ($2, (($4, $6) :: $7))}
 |IF expr THEN expr ELSE expr {IfElse($2,$4,$6)}
 |arith_expr EQ arith_expr {EBin (OpEq, $1, $3)}
 |arith_expr LE arith_expr {EBin (OpL, $1, $3)}
 |arith_expr DCOLON expr {ECons ($1, $3)}
 |arith_expr {$1}
 |LPAR expr COMMA expr pairs {EPair ($2 :: $4 :: $5)}
;

lr:
 |atlr AND lr {$1 :: $3}
 |atlr AND atlr {$1 :: $3 :: []}

atlr:
 |ID ID EQ expr        {(VString $1, VString $2, $4)}
;

arith_expr:
 |arith_expr PLUS factor_expr { EBin (OpAdd, $1, $3)}
 |arith_expr MINUS factor_expr {EBin (OpSub, $1, $3)}
 |factor_expr { $1 }
;

factor_expr:
 |factor_expr MUL app_expr { EBin (OpMul, $1, $3)}
 |factor_expr DIV app_expr {EBin (OpDiv, $1, $3)}
 |app_expr {$1}
;

app_expr:
 |app_expr atomic_expr {EApp ($1, $2)}
 |atomic_expr {$1}

atomic_expr:
 | INT       {EValue (VInt $1)}
 | BOOL      {EValue (VBool $1)}
 | ID        {EId (VString $1)}
 | NIL       {ENil}
 | LPAR expr RPAR { $2 }
;

pats:
 |BAR pattern ARROW expr pats {($2, $4) :: $5}
 |END                         {[]}
;

pattern:
 | at_pat DCOLON pattern    {Pl ($1, $3)}
 | LPAR pattern COMMA pattern ppairs  {Pp ($2 :: $4 :: $5)}
 | at_pat {$1}
;

at_pat:
 | INT       {Pv (VInt $1)}
 | BOOL      {Pv (VBool $1)}
 | ID        {Pv (VId (VString $1))}
 | NIL       {Pv (VNil)}
 | LPAR pattern RPAR {$2}
;

pairs:
 |COMMA expr pairs {$2 :: $3}
 |RPAR {[]}
;

ppairs:
 |COMMA pattern ppairs {$2 :: $3}
 |RPAR {[]}

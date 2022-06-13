type token =
  | INT of (int)
  | ID of (string)
  | BOOL of (bool)
  | IF
  | THEN
  | ELSE
  | LET
  | IN
  | FUN
  | REC
  | AND
  | MATCH
  | WITH
  | BAR
  | END
  | ARROW
  | PLUS
  | MINUS
  | MUL
  | DIV
  | EQ
  | LE
  | LPAR
  | RPAR
  | COMMA
  | NIL
  | DCOLON
  | COMEND
  | EOF

open Parsing;;
let _ = parse_error;;
# 1 "ExprParser.mly"
open Syntax
# 37 "ExprParser.ml"
let yytransl_const = [|
  260 (* IF *);
  261 (* THEN *);
  262 (* ELSE *);
  263 (* LET *);
  264 (* IN *);
  265 (* FUN *);
  266 (* REC *);
  267 (* AND *);
  268 (* MATCH *);
  269 (* WITH *);
  270 (* BAR *);
  271 (* END *);
  272 (* ARROW *);
  273 (* PLUS *);
  274 (* MINUS *);
  275 (* MUL *);
  276 (* DIV *);
  277 (* EQ *);
  278 (* LE *);
  279 (* LPAR *);
  280 (* RPAR *);
  281 (* COMMA *);
  282 (* NIL *);
  283 (* DCOLON *);
  284 (* COMEND *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* INT *);
  258 (* ID *);
  259 (* BOOL *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\001\000\001\000\001\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\003\000\003\000\008\000\006\000\006\000\006\000\009\000\009\000\
\009\000\010\000\010\000\011\000\011\000\011\000\011\000\011\000\
\005\000\005\000\004\000\004\000\004\000\012\000\012\000\012\000\
\012\000\012\000\007\000\007\000\013\000\013\000\000\000"

let yylen = "\002\000\
\005\000\007\000\004\000\002\000\002\000\004\000\006\000\008\000\
\005\000\007\000\006\000\003\000\003\000\003\000\001\000\005\000\
\003\000\003\000\004\000\003\000\003\000\001\000\003\000\003\000\
\001\000\002\000\001\000\001\000\001\000\001\000\001\000\003\000\
\005\000\001\000\003\000\005\000\001\000\001\000\001\000\001\000\
\001\000\003\000\003\000\001\000\003\000\001\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\028\000\030\000\029\000\000\000\000\000\000\000\
\000\000\000\000\031\000\047\000\000\000\000\000\000\000\000\000\
\027\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\004\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\026\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\032\000\000\000\000\000\000\000\
\000\000\000\000\014\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\003\000\000\000\006\000\
\038\000\040\000\039\000\000\000\041\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\001\000\000\000\009\000\000\000\
\017\000\000\000\000\000\000\000\000\000\044\000\000\000\016\000\
\000\000\011\000\007\000\000\000\000\000\042\000\000\000\000\000\
\035\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\
\034\000\010\000\043\000\008\000\019\000\046\000\000\000\036\000\
\000\000\000\000\000\000\045\000\000\000\033\000"

let yydgoto = "\002\000\
\012\000\013\000\041\000\070\000\106\000\014\000\088\000\042\000\
\015\000\016\000\017\000\071\000\112\000"

let yysindex = "\032\000\
\052\255\000\000\000\000\000\000\000\000\100\255\011\255\036\255\
\100\255\100\255\000\000\000\000\004\000\097\255\027\255\014\255\
\000\000\012\255\043\255\020\255\048\255\042\255\047\255\255\254\
\000\000\000\000\014\255\014\255\014\255\014\255\100\255\014\255\
\014\255\100\255\000\000\049\255\077\255\100\255\100\255\082\255\
\248\254\075\255\100\255\064\255\000\000\100\255\027\255\027\255\
\045\255\045\255\000\000\014\255\014\255\071\255\100\255\103\255\
\098\255\102\255\000\255\089\255\100\255\000\000\111\255\000\000\
\000\000\000\000\000\000\064\255\000\000\101\255\093\255\044\255\
\108\255\104\255\100\255\100\255\000\000\100\255\000\000\120\255\
\000\000\075\255\057\255\100\255\064\255\000\000\100\255\000\000\
\100\255\000\000\000\000\003\255\106\255\000\000\064\255\062\255\
\000\000\044\255\121\255\100\255\000\000\100\255\067\255\064\255\
\000\000\000\000\000\000\000\000\000\000\000\000\064\255\000\000\
\112\255\067\255\100\255\000\000\062\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\145\000\073\000\001\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\097\000\121\000\
\166\000\187\000\000\000\025\000\049\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\250\254\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\004\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\119\255\000\000\000\000\000\000\000\000\
\000\000\000\000\119\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\252\255\222\255\197\255\014\000\059\000\034\000\070\000\
\066\000\067\000\247\255\000\000\020\000"

let yytablesize = 471
let yytable = "\061\000\
\025\000\019\000\057\000\026\000\023\000\024\000\035\000\076\000\
\083\000\037\000\100\000\018\000\020\000\036\000\003\000\004\000\
\005\000\037\000\037\000\062\000\021\000\037\000\045\000\046\000\
\023\000\097\000\051\000\077\000\081\000\054\000\101\000\018\000\
\001\000\058\000\059\000\103\000\034\000\022\000\064\000\011\000\
\039\000\072\000\035\000\035\000\113\000\032\000\033\000\038\000\
\024\000\040\000\073\000\114\000\003\000\004\000\005\000\006\000\
\079\000\043\000\007\000\044\000\008\000\027\000\028\000\009\000\
\065\000\066\000\067\000\086\000\087\000\055\000\090\000\091\000\
\022\000\092\000\010\000\104\000\105\000\011\000\056\000\096\000\
\094\000\095\000\098\000\060\000\099\000\063\000\068\000\049\000\
\050\000\069\000\110\000\111\000\047\000\048\000\045\000\108\000\
\020\000\109\000\052\000\053\000\003\000\004\000\005\000\006\000\
\074\000\061\000\018\000\075\000\008\000\078\000\117\000\009\000\
\080\000\027\000\028\000\076\000\084\000\029\000\030\000\085\000\
\021\000\093\000\010\000\031\000\089\000\011\000\102\000\115\000\
\100\000\019\000\118\000\107\000\082\000\116\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\015\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\012\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\013\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\025\000\025\000\000\000\
\025\000\000\000\000\000\025\000\000\000\025\000\025\000\025\000\
\000\000\025\000\025\000\025\000\025\000\025\000\025\000\000\000\
\025\000\025\000\000\000\025\000\025\000\023\000\023\000\025\000\
\023\000\000\000\000\000\023\000\000\000\023\000\023\000\023\000\
\000\000\023\000\023\000\023\000\023\000\023\000\023\000\000\000\
\023\000\023\000\000\000\023\000\023\000\024\000\024\000\000\000\
\024\000\000\000\000\000\024\000\000\000\024\000\024\000\024\000\
\000\000\024\000\024\000\024\000\024\000\024\000\024\000\000\000\
\024\000\024\000\000\000\024\000\024\000\022\000\022\000\000\000\
\022\000\000\000\000\000\022\000\000\000\022\000\022\000\022\000\
\000\000\022\000\022\000\000\000\000\000\022\000\022\000\000\000\
\022\000\022\000\000\000\022\000\022\000\020\000\020\000\000\000\
\020\000\000\000\000\000\020\000\000\000\020\000\020\000\020\000\
\000\000\020\000\020\000\000\000\000\000\020\000\020\000\000\000\
\020\000\020\000\000\000\020\000\020\000\021\000\021\000\000\000\
\021\000\000\000\000\000\021\000\000\000\021\000\021\000\021\000\
\000\000\021\000\021\000\000\000\000\000\021\000\021\000\000\000\
\021\000\021\000\000\000\021\000\021\000\015\000\015\000\000\000\
\015\000\000\000\000\000\015\000\000\000\015\000\015\000\015\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\015\000\015\000\012\000\012\000\015\000\012\000\000\000\000\000\
\012\000\000\000\012\000\012\000\012\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\012\000\012\000\013\000\
\013\000\012\000\013\000\000\000\000\000\013\000\000\000\013\000\
\013\000\013\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\013\000\013\000\000\000\000\000\013\000"

let yycheck = "\008\001\
\000\000\006\000\037\000\000\000\009\000\010\000\016\000\008\001\
\068\000\016\001\008\001\008\001\002\001\002\001\001\001\002\001\
\003\001\024\001\025\001\028\001\010\001\010\001\024\001\025\001\
\000\000\085\000\031\000\028\001\063\000\034\000\028\001\028\001\
\001\000\038\000\039\000\095\000\023\001\002\001\043\000\026\001\
\021\001\046\000\052\000\053\000\104\000\019\001\020\001\005\001\
\000\000\002\001\055\000\111\000\001\001\002\001\003\001\004\001\
\061\000\016\001\007\001\013\001\009\001\017\001\018\001\012\001\
\001\001\002\001\003\001\024\001\025\001\021\001\075\000\076\000\
\000\000\078\000\023\001\014\001\015\001\026\001\002\001\084\000\
\024\001\025\001\087\000\002\001\089\000\011\001\023\001\029\000\
\030\000\026\001\024\001\025\001\027\000\028\000\024\001\100\000\
\000\000\102\000\032\000\033\000\001\001\002\001\003\001\004\001\
\002\001\008\001\007\001\006\001\009\001\021\001\115\000\012\001\
\002\001\017\001\018\001\008\001\016\001\021\001\022\001\027\001\
\000\000\002\001\023\001\027\001\021\001\026\001\021\001\016\001\
\008\001\011\001\117\000\098\000\063\000\114\000\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\000\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\000\000\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\000\000\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\005\001\006\001\255\255\
\008\001\255\255\255\255\011\001\255\255\013\001\014\001\015\001\
\255\255\017\001\018\001\019\001\020\001\021\001\022\001\255\255\
\024\001\025\001\255\255\027\001\028\001\005\001\006\001\028\001\
\008\001\255\255\255\255\011\001\255\255\013\001\014\001\015\001\
\255\255\017\001\018\001\019\001\020\001\021\001\022\001\255\255\
\024\001\025\001\255\255\027\001\028\001\005\001\006\001\255\255\
\008\001\255\255\255\255\011\001\255\255\013\001\014\001\015\001\
\255\255\017\001\018\001\019\001\020\001\021\001\022\001\255\255\
\024\001\025\001\255\255\027\001\028\001\005\001\006\001\255\255\
\008\001\255\255\255\255\011\001\255\255\013\001\014\001\015\001\
\255\255\017\001\018\001\255\255\255\255\021\001\022\001\255\255\
\024\001\025\001\255\255\027\001\028\001\005\001\006\001\255\255\
\008\001\255\255\255\255\011\001\255\255\013\001\014\001\015\001\
\255\255\017\001\018\001\255\255\255\255\021\001\022\001\255\255\
\024\001\025\001\255\255\027\001\028\001\005\001\006\001\255\255\
\008\001\255\255\255\255\011\001\255\255\013\001\014\001\015\001\
\255\255\017\001\018\001\255\255\255\255\021\001\022\001\255\255\
\024\001\025\001\255\255\027\001\028\001\005\001\006\001\255\255\
\008\001\255\255\255\255\011\001\255\255\013\001\014\001\015\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\024\001\025\001\005\001\006\001\028\001\008\001\255\255\255\255\
\011\001\255\255\013\001\014\001\015\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\024\001\025\001\005\001\
\006\001\028\001\008\001\255\255\255\255\011\001\255\255\013\001\
\014\001\015\001\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\024\001\025\001\255\255\255\255\028\001"

let yynames_const = "\
  IF\000\
  THEN\000\
  ELSE\000\
  LET\000\
  IN\000\
  FUN\000\
  REC\000\
  AND\000\
  MATCH\000\
  WITH\000\
  BAR\000\
  END\000\
  ARROW\000\
  PLUS\000\
  MINUS\000\
  MUL\000\
  DIV\000\
  EQ\000\
  LE\000\
  LPAR\000\
  RPAR\000\
  COMMA\000\
  NIL\000\
  DCOLON\000\
  COMEND\000\
  EOF\000\
  "

let yynames_block = "\
  INT\000\
  ID\000\
  BOOL\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 29 "ExprParser.mly"
                        (Let (VString _2, _4))
# 314 "ExprParser.ml"
               : Syntax.command))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 30 "ExprParser.mly"
                               (LetRec (VString _3, VString _4, _6))
# 323 "ExprParser.ml"
               : Syntax.command))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'lr) in
    Obj.repr(
# 31 "ExprParser.mly"
                    (LetRecAnd _3)
# 330 "ExprParser.ml"
               : Syntax.command))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 32 "ExprParser.mly"
              (CExp _1)
# 337 "ExprParser.ml"
               : Syntax.command))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 33 "ExprParser.mly"
           (CExp _1)
# 344 "ExprParser.ml"
               : Syntax.command))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 37 "ExprParser.mly"
                    (EFun (VString _2, _4))
# 352 "ExprParser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 38 "ExprParser.mly"
                         (LetIn (VString _2, _4, _6))
# 361 "ExprParser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 39 "ExprParser.mly"
                                (ERecIn (VString _3, VString _4, _6, _8))
# 371 "ExprParser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'lr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 40 "ExprParser.mly"
                     (ERecAndIn (_3, _5))
# 379 "ExprParser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'pattern) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'pats) in
    Obj.repr(
# 41 "ExprParser.mly"
                                          (EMatch (_2, ((_4, _6) :: _7)))
# 389 "ExprParser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 42 "ExprParser.mly"
                              (IfElse(_2,_4,_6))
# 398 "ExprParser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arith_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'arith_expr) in
    Obj.repr(
# 43 "ExprParser.mly"
                           (EBin (OpEq, _1, _3))
# 406 "ExprParser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arith_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'arith_expr) in
    Obj.repr(
# 44 "ExprParser.mly"
                           (EBin (OpL, _1, _3))
# 414 "ExprParser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arith_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 45 "ExprParser.mly"
                         (ECons (_1, _3))
# 422 "ExprParser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'arith_expr) in
    Obj.repr(
# 46 "ExprParser.mly"
             (_1)
# 429 "ExprParser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'pairs) in
    Obj.repr(
# 47 "ExprParser.mly"
                             (EPair (_2 :: _4 :: _5))
# 438 "ExprParser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atlr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'lr) in
    Obj.repr(
# 51 "ExprParser.mly"
              (_1 :: _3)
# 446 "ExprParser.ml"
               : 'lr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atlr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'atlr) in
    Obj.repr(
# 52 "ExprParser.mly"
                (_1 :: _3 :: [])
# 454 "ExprParser.ml"
               : 'lr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 55 "ExprParser.mly"
                       ((VString _1, VString _2, _4))
# 463 "ExprParser.ml"
               : 'atlr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arith_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'factor_expr) in
    Obj.repr(
# 59 "ExprParser.mly"
                              ( EBin (OpAdd, _1, _3))
# 471 "ExprParser.ml"
               : 'arith_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arith_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'factor_expr) in
    Obj.repr(
# 60 "ExprParser.mly"
                               (EBin (OpSub, _1, _3))
# 479 "ExprParser.ml"
               : 'arith_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'factor_expr) in
    Obj.repr(
# 61 "ExprParser.mly"
              ( _1 )
# 486 "ExprParser.ml"
               : 'arith_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'factor_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'app_expr) in
    Obj.repr(
# 65 "ExprParser.mly"
                           ( EBin (OpMul, _1, _3))
# 494 "ExprParser.ml"
               : 'factor_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'factor_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'app_expr) in
    Obj.repr(
# 66 "ExprParser.mly"
                           (EBin (OpDiv, _1, _3))
# 502 "ExprParser.ml"
               : 'factor_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'app_expr) in
    Obj.repr(
# 67 "ExprParser.mly"
           (_1)
# 509 "ExprParser.ml"
               : 'factor_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'app_expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'atomic_expr) in
    Obj.repr(
# 71 "ExprParser.mly"
                       (EApp (_1, _2))
# 517 "ExprParser.ml"
               : 'app_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atomic_expr) in
    Obj.repr(
# 72 "ExprParser.mly"
              (_1)
# 524 "ExprParser.ml"
               : 'app_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 75 "ExprParser.mly"
             (EValue (VInt _1))
# 531 "ExprParser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : bool) in
    Obj.repr(
# 76 "ExprParser.mly"
             (EValue (VBool _1))
# 538 "ExprParser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 77 "ExprParser.mly"
             (EId (VString _1))
# 545 "ExprParser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 78 "ExprParser.mly"
             (ENil)
# 551 "ExprParser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 79 "ExprParser.mly"
                  ( _2 )
# 558 "ExprParser.ml"
               : 'atomic_expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'pattern) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'pats) in
    Obj.repr(
# 83 "ExprParser.mly"
                              ((_2, _4) :: _5)
# 567 "ExprParser.ml"
               : 'pats))
; (fun __caml_parser_env ->
    Obj.repr(
# 84 "ExprParser.mly"
                              ([])
# 573 "ExprParser.ml"
               : 'pats))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'at_pat) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'pattern) in
    Obj.repr(
# 88 "ExprParser.mly"
                            (Pl (_1, _3))
# 581 "ExprParser.ml"
               : 'pattern))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'pattern) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'pattern) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'ppairs) in
    Obj.repr(
# 89 "ExprParser.mly"
                                      (Pp (_2 :: _4 :: _5))
# 590 "ExprParser.ml"
               : 'pattern))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'at_pat) in
    Obj.repr(
# 90 "ExprParser.mly"
          (_1)
# 597 "ExprParser.ml"
               : 'pattern))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 94 "ExprParser.mly"
             (Pv (VInt _1))
# 604 "ExprParser.ml"
               : 'at_pat))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : bool) in
    Obj.repr(
# 95 "ExprParser.mly"
             (Pv (VBool _1))
# 611 "ExprParser.ml"
               : 'at_pat))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 96 "ExprParser.mly"
             (Pv (VId (VString _1)))
# 618 "ExprParser.ml"
               : 'at_pat))
; (fun __caml_parser_env ->
    Obj.repr(
# 97 "ExprParser.mly"
             (Pv (VNil))
# 624 "ExprParser.ml"
               : 'at_pat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'pattern) in
    Obj.repr(
# 98 "ExprParser.mly"
                     (_2)
# 631 "ExprParser.ml"
               : 'at_pat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'pairs) in
    Obj.repr(
# 102 "ExprParser.mly"
                   (_2 :: _3)
# 639 "ExprParser.ml"
               : 'pairs))
; (fun __caml_parser_env ->
    Obj.repr(
# 103 "ExprParser.mly"
       ([])
# 645 "ExprParser.ml"
               : 'pairs))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'ppairs) in
    Obj.repr(
# 107 "ExprParser.mly"
                       (_2 :: _3)
# 653 "ExprParser.ml"
               : 'ppairs))
; (fun __caml_parser_env ->
    Obj.repr(
# 108 "ExprParser.mly"
       ([])
# 659 "ExprParser.ml"
               : 'ppairs))
(* Entry main *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let main (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Syntax.command)

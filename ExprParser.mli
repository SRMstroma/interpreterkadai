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

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Syntax.command

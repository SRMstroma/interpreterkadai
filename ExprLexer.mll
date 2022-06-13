{
 open ExprParser
}

let digit = ['0' - '9']
let space = ' ' | '\t' | '\r' | '\n'
let alpha = ['a' - 'z' 'A' - 'Z' '_']
let ident = alpha (alpha | digit)*

rule token = parse
  |space+        { token lexbuf }
  |"fun"         { FUN }
  |"if"          { IF }
  |"then"        { THEN }
  |"else"        { ELSE }
  |"true"        { BOOL true}
  |"false"       { BOOL false}
  |"let"         { LET }
  |"in"          { IN }
  |"rec"         { REC }
  |"match"       { MATCH }
  |"with"        { WITH }
  |"end"         { END }
  |"and"         { AND }
  |"->"          { ARROW }
  |"="           { EQ }
  |"<"           { LE }
  |'+'           { PLUS }
  |'-'           { MINUS }
  |'*'           { MUL }
  |'/'           { DIV }
  |'('           { LPAR }
  |')'           { RPAR }
  |'|'           { BAR }
  |','           { COMMA }
  |"[]"          { NIL }
  |"::"          { DCOLON }
  |";;"          { COMEND }
  |digit+ as n   { INT (int_of_string n) }
  |ident as n    { ID n }
  |eof           { EOF }
  |_             {failwith ("Unknown Token: " ^ Lexing.lexeme lexbuf)}

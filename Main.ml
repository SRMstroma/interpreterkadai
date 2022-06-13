open Syntax
open ExprParser
open ExprLexer

let filename = ref ""
let fop = ref false(*いらなかったかもしれません*)
let envi = ref []
let tyenvi = ref []

let main () =(*こっちはファイル読み込まないやつです*)
 try
  let lexbuf = Lexing.from_channel stdin in
  while true do
  let result = ExprParser.main ExprLexer.token lexbuf in
  let (prc, newc) = infer_cmd !tyenvi result in
  tyenvi := newc;print_tys prc;
  print_command (ev envi result); print_newline();
  done
 with
  | Parsing.Parse_error ->
    print_endline "Parse Error!"
;;

let textofline:in_channel -> string = fun ch ->
let rec tol:in_channel -> string -> string = fun ch -> fun st ->
  try
  tol ch (st ^ " " ^ input_line ch)
  with End_of_file -> st
in tol ch "";;

let stc:string -> string list = fun st ->
let rec string_to_commands s bs n f =
 try (if s.[n] = ';' then if f then ((bs ^ ";") :: string_to_commands s "" (n+1) false)
                          else string_to_commands s (bs ^ ";") (n+1) true
      else string_to_commands s (bs ^ Char.escaped s.[n]) (n+1) false)
 with Invalid_argument _ -> if bs = "" then [] else bs :: []
in string_to_commands st "" 0 false;;

let fmain ch =
 try
  let fst = textofline ch in
  let coms = stc fst in
  let rec evals c = match c with
  [] -> close_in ch
  |co :: rest ->
  let lexbuf = Lexing.from_string co in
  let result = ExprParser.main ExprLexer.token lexbuf in
  let (prc, newc) = infer_cmd !tyenvi result in
  tyenvi := newc;print_tys prc;
  print_command (ev envi result); print_newline();evals rest
  in evals coms
 with
  | Parsing.Parse_error ->
    print_endline "Parse Error!"
;;

if !Sys.interactive then
 ()
else
 Arg.parse [] (fun s -> filename := s;) "Usage: main filename";
 let {contents = fn} = filename in
 if fn = "" then while true do main () done else fop := true;let c = open_in fn in fmain c

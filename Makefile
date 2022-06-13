SOURCES = syntax.ml ExprLexer.mll ExprParser.mly Main.ml
RESULT  = main

YFLAGS = -v 

all: byte-code byte-code-library

-include OCamlMakefile

CCC ?= ocamlopt -g -S -inline 20 -nodynlink -annot -ccopt -O3 -ccopt -mtune=native -ccopt -flto
JAVALIBDIR=`ocamlfind query javalib`
SRC=checkpoint.ml

all: checkpoint

checkpoint:
	ocamlfind $(CCC) -pp "camlp4o pa_macro.cmo -DDEBUG" -package extlib,deriving -package sawja -package batteries -package javalib \
	-linkpkg $(SRC) -o $@


clean:
	rm -rf *.cm* *.o *.a *.annot *.log checkpoint *.class *.s *.ini*

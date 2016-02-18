CCC ?= ocamlopt -g -S -inline 20 -nodynlink -annot -ccopt -O3 -ccopt -mtune=native -ccopt -flto
# WCMADIR += /home/amal029/AUCKLAND_WORK/Nadeem/TDMA
# WCMA=wcma.cmxa
# JOPLANG=joplang.cmxa
SRC=checkpoint.ml

all: checkpoint

checkpoint:
	ocamlfind $(CCC) -pp "camlp4o pa_macro.cmo -DDEBUG" -package	\
	extlib,deriving,sawja,batteries,javalib -linkpkg $(SRC) -o $@


clean:
	rm -rf *.cm* *.o *.a *.annot *.log checkpoint *.class *.s *.ini*

TARGET=Real01Add2.vo RealMulDivPow.vo RealAddGrp.vo RealComplete.vo Real01Mul.vo RealDiv.vo
FILESFORDEP=`LC_ALL=C ls *.v`

all: $(TARGET)

ocaml:
	ocamlopt.opt -pp camlp5r real2.ml

clean:
	rm -f *.glob *.vo *.cm[iox] *.out *.o

depend:
	mv .depend .depend.bak
	coqdep -I . $(FILESFORDEP) | LC_ALL=C sort > .depend

.SUFFIXES: .v .vo .ml .cmo

.v.vo:
	coqc $<

.ml.cmo:
	ocamlc -pp camlp5r -c $<

.PHONY: all

include .depend

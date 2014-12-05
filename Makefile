TARGET=Real01Mul.vo
FILESFORDEP=`LC_ALL=C ls *.v`

all: $(TARGET)

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

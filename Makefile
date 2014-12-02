TARGET=Real01Mul.vo
FILESFORDEP=`LC_ALL=C ls *.v`

all: $(TARGET)

clean:
	rm -f *.glob *.vo

depend:
	mv .depend .depend.bak
	coqdep -I . $(FILESFORDEP) | LC_ALL=C sort > .depend

.SUFFIXES: .v .vo

.v.vo:
	coqc -I ../puiseuxth/coq $<

.PHONY: all

include .depend

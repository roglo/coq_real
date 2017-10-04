TARGET=FracReal.vo
FILESFORDEP=`LC_ALL=C ls *.v`

all: $(TARGET)

clean:
	rm -f *.glob *.vo *.cm[iox] *.out *.o

depend:
	mv .depend .depend.bak
	coqdep $(FILESFORDEP) | LC_ALL=C sort > .depend

.SUFFIXES: .v .vo

.v.vo:
	coqc $<

.PHONY: all

include .depend

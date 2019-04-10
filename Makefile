TARGET=UrealAddAssoc.vo
FILESFORDEP=`LC_ALL=C ls *.v`

all: $(TARGET)

doc:
	coqdoc -d html --utf8 -g Rational.v

clean:
	rm -f *.glob *.vo *.cm[iox] *.out *.o
	rm -f .*.bak .*.aux .*.cache

depend:
	mv .depend .depend.bak
	coqdep $(FILESFORDEP) | LC_ALL=C sort > .depend

.SUFFIXES: .v .vo

.v.vo:
	coqc $<

.PHONY: all doc clean depend

include .depend

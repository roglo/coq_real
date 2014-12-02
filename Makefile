all: Real01Add.vo

clean:
	rm -f *.vo

.SUFFIXES: .v .vo

.v.vo:
	coqc -I ../puiseuxth/coq $<

.PHONY: all

all: Real.vo

.SUFFIXES: .v .vo

.v.vo:
	coqc -I ../puiseuxth/coq $<

.PHONY: all

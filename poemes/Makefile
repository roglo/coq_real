LATEXOPTS=-file-line-error -halt-on-error

all: reels.pdf creels.pdf sreels.pdf

main.pdf: always
	pdflatex $(LATEXOPTS) $*.tex
	bibtex $*.aux

always:

clean:
	rm -f *.aux *.dvi *.log *.bbl *.blg *.out
	rm -f *.pdf *.pdf_tex

.SUFFIXES: .ftex .pdf

.ftex.pdf:
	pdflatex $(LATEXOPTS) $*.ftex

.PHONY: all clean always

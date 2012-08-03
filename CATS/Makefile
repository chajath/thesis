.PHONY: all
all: cats.pdf cats.ps

%.pdf:  %.dvi
	dvipdf $<

%.ps:   %.dvi
	dvips $<

cats.dvi: cats.tex duck.bib CRPITStyle.cls harvard.sty agsm.bst
	latex $<
	bibtex $(basename $<)
	latex $<
	latex $<

.PHONY: clean
clean:
	$(RM) *.aux *.bbl *.blg *.thm *.log
	$(RM) *.dvi *.pdf *.ps

theory2: theory2.pdf

theory2.dvi: theory2.tex
	latex $<

theory2.tex: theory2.lyx
	lyx -export latex $@

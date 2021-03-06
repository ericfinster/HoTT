# Edit the following parameter(s) if "make" fails to find the executables

# The directory which contains the Coq executables (leave it empty if
# coqc is in the PATH), for example on my Mac I would set
# COQBIN=/Applications/CoqIdE_8.3.app/Contents/Resources/bin/
COQBIN=

# Edit below at your own risk
COQC:=$(COQBIN)coqc
COQDEP:=$(COQBIN)coqdep
COQDOC:=$(COQBIN)coqdoc

# The list of files that comprise the library in the order in which
# they should appear in the generated documentation.

VFILES:= Integers.v Circle.v Pi1S1.v IsInhab.v

VOFILES:=$(VFILES:.v=.vo)
GLOBFILES:=$(VFILES:.v=.glob)

.PHONY: all .depend html latex pdf

all: .depend $(VOFILES) # doc

clean:
	/bin/rm -f *~ *.vo *.glob *.~ doc/html/* doc/latex/*

doc: html pdf

html: $(GLOBFILES)
	$(COQDOC) --html --toc --utf8 --charset utf8 --interpolate -d doc/html $(VFILES)
	/bin/cp -f homotopy.css doc/html/coqdoc.css
	echo +++++;\
	echo +++++ HMTL documentation doc/html was generated successfully;\
	echo +++++

latex: $(GLOBFILES)
	$(COQDOC) --latex --toc --utf8 --charset utf8 --interpolate -p '\usepackage{amssymb}' -o doc/latex/UnivalentFoundations.tex $(VFILES)
	if [ ! -f doc/latex/coqdoc.sty ] ; then echo coqdoc.sty not found, using my own; cp coqdoc.sty doc/latex; fi

pdf: latex
	if [ -x "`which latexmk`" ]; \
	then \
		echo Good, you have latexmk; \
		cd doc/latex; \
		latexmk -pdf UnivalentFoundations.tex; \
	else \
		echo Using pdflatex to generated PDF; \
		cd doc/latex; \
		pdflatex UnivalentFoundations.tex; \
		pdflatex UnivalentFoundations.tex; \
	fi
	echo +++++;\
	echo +++++ PDF document doc/latex/UnivalentFoundations.pdf was generated successfully;\
	echo +++++

.depend:
	$(COQDEP) -I .. -I . $(VFILES) > .depend

%.vo %.glob: %.v .depend
	$(COQC) -I .. -I . $<

include .depend

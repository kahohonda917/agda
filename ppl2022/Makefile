.SUFFIXES: .tex .pdf .all .dvi .ps

.DELETE_ON_ERROR:

all :
	@echo usage: make filename.pdf / make clean

.tex.all :
	platex $<
	pbibtex $*
	platex $<
	platex $<
	dvipdfmx $*

.tex.dvi :
	platex $<
	if grep "No file $*.bbl." $*.log ||\
	   grep 'There were undefined references.' $*.log ;\
	then\
	  pbibtex $* ;\
	  platex $< ;\
	fi
	while grep 'Rerun to get ' $*.log ; do\
	  platex $< ;\
	done

.dvi.pdf :
	dvipdfmx $<

.dvi.ps :
	dvips -o $*.ps $<

clean :
	rm -f *.ps *.bak *.dvi *.aux *.log *.toc *.idx *.nav *.out *.snm *.vrb *.ptb *.ilg *.ind *.bbl *.blg *.pag *~

-include .depend

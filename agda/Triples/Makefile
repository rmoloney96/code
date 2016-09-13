STDLIB=/home/francoisbabeuf/lib/agda-stdlib/src/
FINSET=/home/francoisbabeuf/lib/parser-combinators.code/
example :
	agda --compile -i $(STDLIB) Example.agda -i $(FINSET)
paper:
	agda --latex MuPaper.lagda
	cd latex ; pdflatex MuPaper.tex

PARAMS =
LISTINGS =
DIAGRAMS =

all: out/report.pdf

clear:
	rm -rf out/*

out/%.tex: %.md %_template.tex references.bib
	pandoc  --template=$*_template.tex \
		--variable monofont=Menlo \
		--latex-engine=xelatex \
		--number-sections \
		--table-of-contents \
		--bibliography=references.bib \
		--natbib \
		--metadata biblio-style=alpha \
		$(PARAMS) \
		-f markdown -t latex \
		$< -o $@

aux/%.tex: %.md
	pandoc --latex-engine=xelatex \
	       -f markdown -t latex \
	       $< -o $@

out/report.tex : $(LISTINGS:%.md=aux/%.tex) $(DIAGRAMS)

count: out/report.tex
	texcount -sum=1,0,0,0,0,0,0 -col out/report.tex

out/%.pdf: out/%.tex references.bib
	latex -output-directory=out out/$*
	# bibtex out/$*
	# latex -output-directory=out out/$*
	pdflatex -output-directory=out out/$*

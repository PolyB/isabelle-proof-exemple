TEX = pdflatex -shell-escape -interaction=nonstopmode -file-line-error

all: slides.pdf

slides.pdf: slides.tex
	$(TEX) slides
	$(TEX) slides

clean:
	$(RM) *.log *.aux *.pdf

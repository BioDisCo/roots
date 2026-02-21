TARGETS = lem7 lem8 lem9 steiner

all: $(TARGETS:%=%.svg)

%.svg: %.pdf
	inkscape $< --export-type=svg --export-plain-svg --export-filename=$@

%.pdf: %.tex
	pdflatex $*

clean:
	rm *.aux *.pdf *.svg *.log
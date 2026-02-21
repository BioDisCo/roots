PDFS := $(patsubst %.svg,%.pdf,$(wildcard panel_*.svg))

all: $(PDFS)

panel_%.pdf: panel_%.svg
	inkscape $< --export-type=pdf --export-filename=$@

clean:
	rm results/*.pdf

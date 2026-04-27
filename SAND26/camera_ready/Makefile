TARGETS=main.pdf
BADGE_SVGS=$(wildcard badges/*.svg)
BADGE_PDFS=$(BADGE_SVGS:.svg=.pdf)

# You want latexmk to *always* run, because make does not have all the info.
# Also, include non-file targets in .PHONY so they are run regardless of any
# file of the given name existing.
.PHONY: all clean $(TARGETS)

# The first rule in a Makefile is the one executed by default ("make"). It
# should always be the "all" rule, so that "make" and "make all" are identical.
#
# -pdf tells latexmk to generate PDF directly (instead of DVI).
# -pdflatex="" tells latexmk to call a specific backend with specific options.
# -use-make tells latexmk to call make for generating missing files.

# -interaction=nonstopmode keeps the pdflatex backend from stopping at a
# missing file reference and interactively asking you for an alternative.
all: $(BADGE_PDFS) $(TARGETS)

badges/%.pdf: badges/%.svg
	inkscape $< --export-type=pdf --export-filename=$@

$(TARGETS): $(BADGE_PDFS)
	latexmk -pdf -pdflatex="pdflatex -interaction=nonstopmode" -use-make $(@:.pdf=.tex)


clean:
	latexmk -CA
	rm -f *.bbl *.aux *.axp *.vtc
	rm -f $(BADGE_PDFS)

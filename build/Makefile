rules = pdf print

targets = $(addsuffix .pdf,$(rules))

$(targets): %.pdf: tex/%.tex .current-revision
	echo q | xelatex tex/$*.tex || echo 0
	echo q | xelatex tex/$*.tex || echo 0

missing-from-sample.pdf: ../format/missing-from-sample.tex
	xelatex ../format/missing-from-sample.tex


.current-revision: git-revision
	git rev-parse --short HEAD | tr -d '\n' > .current-revision
	echo -n "+" >> .current-revision
	git rev-list --count HEAD >> .current-revision

.PHONY: git-revision clean

clean:
	rm tex/*.tex || echo ""
	rm *.aux || echo ""
	rm *.pdf || echo ""
	rm *.epub || echo ""


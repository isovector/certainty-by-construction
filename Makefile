RULES := pdf epub sample
CONTENT := book

PANDOC_OPTS := -F pandoc-crossref \
               --citeproc \
               --filter design-tools-exe \
               --from markdown+fancy_lists+raw_tex+raw_html \
               --bibliography=bibliography.bib \
               -M link-citations \
               --tab-stop=100 \
               --no-highlight \
               --top-level-division=part

PANDOC_PDF_OPTS := --from latex+raw_tex \
                   --template format/tex/template.tex \
                   --toc \
                   -s \
                   --top-level-division=chapter \
                   -t latex+lagda

PANDOC_EPUB_OPTS := --from markdown+fancy_lists+raw_html \
                    -F pandoc-crossref \
                    --toc \
                    --citeproc \
                    -s \
                    --css=format/epub/css.css \
                    --epub-cover-image art/epub-cover.png \
                    -M title="Certainty by Construction" \
                    -M subtitle="Software & Mathematics in Agda" \
                    -M author="Sandy Maguire" \
                    -M publisher="Cofree Press" \
                    -M rights="© 2023 Sandy Maguire" \
                    --top-level-division=chapter \
                    -f html-native_spans+raw_html \
                    -t epub

ALL_CHAPTERS := Chapter00-preface \
                Chapter0-coblub \
                Chapter1-Agda \
                Chapter2-Numbers \
                Chapter3-Proofs \
                Chapter4-Relations \
                Chapter5-Modular-Arithmetic \
                Chapter6-Decidability \
                Chapter7-Structures \
                Chapter8-Isomorphisms \
                Chapter9-ProgramOptimization \
                Appendix1-Ring-Solving \
                Bibliography \
                Backmatter

ALL_LITERATE_AGDA := $(patsubst %,src/book/%.lagda.md,$(ALL_CHAPTERS))
ALL_LAGDA_TEX := $(patsubst src/book/%.lagda.md,build/tex/agda/%.lagda.tex,$(ALL_LITERATE_AGDA))
ALL_LAGDA_HTML := $(patsubst src/book/%.lagda.md,build-epub/agda/%.lagda.html,$(ALL_LITERATE_AGDA))
ALL_TEX := $(patsubst src/book/%.lagda.md,build/tex/book/%.tex,$(ALL_LITERATE_AGDA))
ALL_HTML := $(patsubst src/book/%.lagda.md,build-epub/book/%.html,$(ALL_LITERATE_AGDA))
ALL_SOME_HTML := $(patsubst src/book/%.lagda.md,build-epub/agda/html/%.html,$(ALL_LITERATE_AGDA))

SAMPLE_CHAPTERS := Chapter0-coblub \
                   Chapter6-Decidability

SAMPLE_LITERATE_AGDA := $(patsubst %,src/book/%.lagda.md,$(SAMPLE_CHAPTERS))
SAMPLE_LAGDA_TEX := $(patsubst src/book/%.lagda.md,build/tex/agda/%.lagda.tex,$(SAMPLE_LITERATE_AGDA))
SAMPLE_AGDA_TEX := $(patsubst src/book/%,build/tex/agda/%,$(wildcard src/book/*.agda))
SAMPLE_TEX := $(patsubst src/book/%.lagda.md,build/tex/book/%.tex,$(SAMPLE_LITERATE_AGDA))

# $(RULES): %: build/%.pdf

pdf : build/pdf.pdf
print : build/print.pdf
sample : build/sample.pdf
epub : build/epub.epub

all : build/pdf.pdf build/print.pdf build/sample.pdf build-epub.epub

# -- Source the files
# Transpile markdown to latex
build/tex/agda/%.lagda.tex : src/book/%.lagda.md
	pandoc $(PANDOC_OPTS) -t latex+lagda -o $@ $^

# Just copy for html
build-epub/agda/%.lagda.md : src/book/%.lagda.md
	pandoc $(PANDOC_OPTS) -t html+lagda -o $@ $^

# -- Run the agda processor
# TEX
build/tex/agda/latex/%.tex : build/tex/agda/%.lagda.tex
	(cd build/tex/agda && agda --latex $*.lagda.tex)
	(grep UnsolvedMeta $@ > /dev/null && scripts/fix-metaspan.sh $@) || echo "ok"

# HTML
build-epub/agda/html/%.md : build-epub/agda/%.lagda.md
	(cd build-epub/agda && agda --html --html-highlight=code $*.lagda.md)

build-epub/agda/html/%.html : build-epub/agda/html/%.md
	cp $^ $@

# -- Copy the resulting documents
# TEX
build/tex/book/%.tex : build/tex/agda/latex/%.tex
	mv $^ $@

# HTML
build-epub/book/%.html : build-epub/agda/html/%.html
	cp $^ $@
	sed -i 's/⅋[^ {}()._\\<>"]*//g' $@
	sed -i 's/&#8523;[^ {}()._\\<>"]*//g' $@
	sed -i 's/id="\([^"]\+\)"//g' $@
	sed -i 's/href="\([^"]\+\)"//g' $@
	sed -i 's/doc-endnotes/doc-footnote/g' $@

build/.design-tools :
	mkdir build/.design-tools


# -- Compile all the resulting latex documents together
# TEX
build/tex/pdf.tex : $(ALL_TEX) format/tex/template.tex build/.design-tools Makefile
	cp .design-tools/*.png build/.design-tools
	pandoc $(PANDOC_PDF_OPTS) -M wants-cover -V wants-cover -o $@ $(ALL_TEX)
	sed -i 's/\AgdaComment{--\\ !\\ \([0-9]\)}/annotate{\1}/g' $@
	sed -i 's/\AgdaPostulate{Level}/\AgdaFunction{Level}/g' $@
	sed -i 's/\\hypertarget{fig:\([^}]\+\)}{}//g' $@
	sed -i 's/⅋[^ {}()._\\]*//g' $@
	sed -i 's/VERYILLEGALCODE/code/g' $@
	sed -i '/{part}/d' $@

build/tex/print.tex : $(ALL_TEX) format/tex/template.tex build/.design-tools Makefile
	cp .design-tools/*.png build/.design-tools
	pandoc $(PANDOC_PDF_OPTS) -o $@ $(ALL_TEX)
	sed -i 's/\AgdaComment{--\\ !\\ \([0-9]\)}/annotate{\1}/g' $@
	sed -i 's/\AgdaPostulate{Level}/\AgdaFunction{Level}/g' $@
	sed -i 's/\\hypertarget{fig:\([^}]\+\)}{}//g' $@
	sed -i 's/⅋[^ {}()._\\]*//g' $@
	sed -i 's/VERYILLEGALCODE/code/g' $@
	sed -i '/{part}/d' $@

# HTML
build-epub/epub.epub : $(ALL_HTML) format/epub/metadata.md build/.design-tools Makefile format/epub/css.css
	cp .design-tools/*.png build/.design-tools
	pandoc $(PANDOC_EPUB_OPTS) -o $@ $(ALL_HTML)

build/epub.epub : build-epub/epub.epub
	cp $^ $@

build/tex/sample.tex : $(SAMPLE_TEX) format/tex/template.tex build/.design-tools Makefile
	cp .design-tools/*.png build/.design-tools
	pandoc $(PANDOC_PDF_OPTS) -M wants-cover -V wants-cover -o $@ $(SAMPLE_TEX)
	sed -i 's/\AgdaComment{--\\ !\\ \([0-9]\)}/annotate{\1}/g' $@
	sed -i 's/\AgdaPostulate{Level}/\AgdaFunction{Level}/g' $@
	sed -i 's/\\hypertarget{fig:\([^}]\+\)}{}//g' $@
	sed -i 's/⅋[^ {}()._\\]*//g' $@
	sed -i 's/VERYILLEGALCODE/code/g' $@
	sed -i '/{part}/d' $@

# Copy the agda style
build/tex/agda.sty : format/tex/agda.sty
	cp $^ $@

# Build the pdf!
build/pdf.pdf :  $(ALL_LAGDA_TEX) build/tex/pdf.tex build/tex/agda.sty art/cover.pdf
	make -C build pdf.pdf

build/print.pdf :  $(ALL_LAGDA_TEX) build/tex/print.tex build/tex/agda.sty
	make -C build print.pdf

# Build the sample!!
build/sample.pdf :  $(SAMPLE_LAGDA_TEX) $(SAMPLE_AGDA_TEX) build/tex/sample.tex build/tex/agda.sty art/cover.pdf
	make -C build sample.pdf


.NOTINTERMEDIATE: build/tex/agda/%.lagda.tex $(ALL_LAGDA_TEX) $(ALL_LAGDA_HTML) $(ALL_TEX) $(ALL_HTML) $(ALL_SOME_HTML)

.PHONY: clean clean-epub all $(RULES) refresh-epub

refresh-epub:
	rm build-epub/book/*.html

clean-epub:
	rm -r build-epub/agda/* || echo 0
	rm -r build-epub/agda/html/* || echo 0
	rm -r build-epub/book/* || echo 0
	rm build/epub.epub || echo 0
	rm build-epub/epub.epub || echo 0

clean:
	rm -r build/tex/agda/*
	rm -r build/tex/book/*
	make -C build clean

RULES := pdf
CONTENT := book
DESIGN_IMAGES := $(addprefix build/,$(wildcard .design-tools/*.png))

PANDOC_OPTS := -F pandoc-crossref \
               --citeproc \
               --filter design-tools-exe \
               --from markdown+fancy_lists+raw_tex \
               -t latex+lagda \
               --tab-stop=100 \
               --no-highlight \
               --top-level-division=part

PANDOC_PDF_OPTS := --from latex+raw_tex \
                   --template format/tex/template.tex \
                   --toc \
                   -s \
                   --top-level-division=chapter \
                   -t latex+lagda


agda := $(wildcard src/book/*.lagda.md)

ALL_LAGDA := $(patsubst src/book/%.lagda.md,build/tex/agda/%.lagda.tex,$(wildcard src/book/*.lagda.md))
ALL_AGDA := $(patsubst src/book/%,build/tex/agda/%,$(wildcard src/book/*.agda))
ALL_TEX := $(patsubst src/book/%.lagda.md,build/tex/book/%.tex,$(wildcard src/book/*.lagda.md))

# $(RULES): %: build/%.pdf
all : build/pdf.pdf

# Transpile markdown to latex
build/tex/agda/%.lagda.tex : src/book/%.lagda.md
	pandoc $(PANDOC_OPTS) -o $@ $^

# Copy non-literate agda into build directory
build/tex/agda/%.agda : src/book/%.agda
	cp $^ $@

# Run the agda processor
build/tex/agda/latex/%.tex : build/tex/agda/%.lagda.tex
	(cd build/tex/agda && agda --latex $*.lagda.tex)
	(grep UnsolvedMeta $@ > /dev/null && scripts/fix-metaspan.sh $@) || echo "ok"

# Copy the resulting latex document
build/tex/book/%.tex : build/tex/agda/latex/%.tex
	mv $^ $@

build/.design-tools :
	mkdir build/.design-tools

# Compile all the resulting latex documents together
build/tex/pdf.tex : $(ALL_TEX) format/tex/template.tex build/.design-tools Makefile
	cp .design-tools/*.png build/.design-tools
	pandoc $(PANDOC_PDF_OPTS) -o $@ $(ALL_TEX)
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
build/pdf.pdf :  $(ALL_LAGDA) $(ALL_AGDA) build/tex/pdf.tex build/tex/agda.sty
	make -C build pdf.pdf






# targets = $(addsuffix .pdf,$(addprefix build/,$(RULES)))
# $(targets): build/%.pdf: build/tex/%.tex
#		make -C build $*.pdf

# sources = $(addsuffix .tex,$(addprefix build/tex/,$(RULES)))
# prose = $(addsuffix /*.lagda.md,$(addprefix src/,$(CONTENT)))
# $(sources): build/tex/%.tex: src/metadata.md src/%.md $(prose) format/tex/template.tex
#		pandoc $(PANDOC_OPTS) $(PANDOC_PDF_OPTS) -o $@ $(filter %.lagda.md,$^)
#		# cp .design-tools/*.png build/.design-tools
#		sed -i 's/\CommentTok{{-}{-} ! \([0-9]\)}/annotate{\1}/g' $@
#		sed -i 's/\CommentTok{{-}{-} .via \([^}]\+\)}/reducevia{\1}/g' $@
#		sed -i 's/\(\\KeywordTok{law} \\StringTok\){"\([^"]\+\)"}/\1{\\lawname{\2}}/g' $@

.NOTINTERMEDIATE: build/tex/agda/%.lagda.tex $(ALL_LAGDA) $(ALL_AGDA)

.PHONY: clean all $(RULES)

clean:
	rm -r build/tex/agda/*
	rm -r build/tex/book/*
	make -C build clean

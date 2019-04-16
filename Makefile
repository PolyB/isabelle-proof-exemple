AUTOCORRES_VERSION=1.5
AUTOCORRES_NAME=autocorres-$(AUTOCORRES_VERSION)

ifndef ISABELLE_BIN
$(error ISABELLE_BIN is not set)
endif

L4V_ARCH:=X64

.PHONY:build-autocorres src/all.c_pp

documentation.pdf: proof/output/document.pdf
	cp $^ $@

build-autocorres: tool/autocorres
	L4V_ARCH=$(L4V_ARCH) $(ISABELLE_BIN) build -d tool/autocorres AutoCorres

tool/autocorres:
	mkdir -p tmp
	curl https://ts.data61.csiro.au/projects/TS/autocorres/$(AUTOCORRES_NAME).tar.gz -o tmp/$(AUTOCORRES_NAME).tar.gz
	mkdir tool
	tar xf tmp/$(AUTOCORRES_NAME).tar.gz -C tool/
	mv tool/$(AUTOCORRES_NAME) tool/autocorres

src/build:
	mkdir src/build
	cd src/build ; cmake ..

src/all.c_pp: src/build
	$(MAKE) -C src/build gen-all-c_pp

proof/output/document.pdf: src/all.c_pp tool/autocorres
	L4V_ARCH=$(L4V_ARCH) $(ISABELLE_BIN) build -D . -g ProofExemples

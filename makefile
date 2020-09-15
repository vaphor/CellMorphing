SRC=src/*
all:vaphor
build/src/main.native: $(SRC)
	ocamlbuild main.native -I src -build-dir build
vaphor: build/src/main.native
	cp $^ $@
clean:
	rm -rf build/
demo: demo.smt2 vaphor
	./vaphor demo.smt2
test: demo.smt2 vaphor
	@mkdir -p build
	./vaphor demo.smt2 > build/demoabs.smt2
	@if [ $$(which z3) = "" ]; then echo "Failed to find z3 solver"; fi
	@which z3  > /dev/null
	@echo "Using z3 solver : $$(which z3)"
	@echo "Result is : " $$(z3 build/demoabs.smt2)
	@echo "Expected is : sat"
	
.PHONY: demo test clean



# 
# 
# 
# OCAMLPREFIX=
# OCAMLC=         $(OCAMLPREFIX)ocamlc
# OCAMLOPT=       $(OCAMLPREFIX)ocamlopt.opt
# OCAMLYACC=      $(OCAMLPREFIX)ocamlyacc -v
# OCAMLLEX=       $(OCAMLPREFIX)ocamllex
# OCAMLDEP=       $(OCAMLPREFIX)ocamldep
# OCAMLINCLUDES=
# OCAMLFLAGS=     -warn-error a -g $(OCAMLINCLUDES)
# OCAMLC=         $(OCAMLPREFIX)ocamlc
# OCAMLOPT=       $(OCAMLPREFIX)ocamlopt.opt
# %.ml: %.mll
# 	$(OCAMLLEX) $*.mll
# %.ml %.mli: %.mly
# 	$(OCAMLYACC) $*.mly
# %.cmo: %.ml %.cmi
# 	$(OCAMLC) $(OCAMLFLAGS) -c $*.ml
# %.cmx: %.ml %.cmi
# 	$(OCAMLOPT) $(OCAMLFLAGS) -c $*.ml
# %.cmi: %.mli
# 	$(OCAMLC) $(OCAMLFLAGS) -c $*.mli
# %.cmo: %.ml
# 	$(OCAMLC) $(OCAMLFLAGS) -c $*.ml
# %.cmx: %.ml
# 	$(OCAMLOPT) $(OCAMLFLAGS) -c $*.ml
# all: vaphor
# AUTOGEN_ML=	horn_parser.ml  horn_lexer.ml
# AUTOGEN_MLI=    horn_parser.mli
# AUTOGEN= $(AUTOGEN_ML) $(AUTOGEN_MLI)
# ML_FILES=	localizing.ml \
#                 helper.ml \
#                 types.ml \
#                 interpret.ml \
#                 transform.ml \
#                 normalization.ml \
#                 abstraction.ml \
#                 simplification.ml \
#                 config.ml \
#                 $(AUTOGEN_ML) \
#                 main.ml
#                 
# CMO_FILES=	$(ML_FILES:%.ml=%.cmo)
# CMX_FILES=      $(ML_FILES:%.ml=%.cmx)
# vaphor: $(CMX_FILES) $(AUTOGEN)
# 	ocamlopt $(CMX_FILES) -o vaphor
# 
# depend: $(AUTOGEN_ML) $(ML_FILES)
# 	ocamldep $(OCAMLINCLUDES) *.mli *.ml */*.mli */*.ml > depend
# clean: 
# 	rm -f *.cmo *.cmi *.cmx */*.cmi */*.cmo */*.cmx && \
# 	rm -f *.o $(AUTOGEN_ML) $(AUTOGEN_MLI) abstract depend *~
# include depend

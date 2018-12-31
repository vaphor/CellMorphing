OCAMLPREFIX=
OCAMLC=         $(OCAMLPREFIX)ocamlc
OCAMLOPT=       $(OCAMLPREFIX)ocamlopt.opt
OCAMLYACC=      $(OCAMLPREFIX)ocamlyacc -v
OCAMLLEX=       $(OCAMLPREFIX)ocamllex
OCAMLDEP=       $(OCAMLPREFIX)ocamldep
OCAMLINCLUDES=
OCAMLFLAGS=     -warn-error a -g $(OCAMLINCLUDES)
OCAMLC=         $(OCAMLPREFIX)ocamlc
OCAMLOPT=       $(OCAMLPREFIX)ocamlopt.opt
%.ml: %.mll
	$(OCAMLLEX) $*.mll
%.ml %.mli: %.mly
	$(OCAMLYACC) $*.mly
%.cmo: %.ml %.cmi
	$(OCAMLC) $(OCAMLFLAGS) -c $*.ml
%.cmx: %.ml %.cmi
	$(OCAMLOPT) $(OCAMLFLAGS) -c $*.ml
%.cmi: %.mli
	$(OCAMLC) $(OCAMLFLAGS) -c $*.mli
%.cmo: %.ml
	$(OCAMLC) $(OCAMLFLAGS) -c $*.ml
%.cmx: %.ml
	$(OCAMLOPT) $(OCAMLFLAGS) -c $*.ml
all: vaphor
AUTOGEN_ML=	horn_parser.ml  horn_lexer.ml
AUTOGEN_MLI=    horn_parser.mli
AUTOGEN= $(AUTOGEN_ML) $(AUTOGEN_MLI)
ML_FILES=	localizing.ml \
                helper.ml \
                types.ml \
                interpret.ml \
                transform.ml \
                normalization.ml \
                abstraction.ml \
                simplification.ml \
                config.ml \
                $(AUTOGEN_ML) \
                main.ml
                
CMO_FILES=	$(ML_FILES:%.ml=%.cmo)
CMX_FILES=      $(ML_FILES:%.ml=%.cmx)
vaphor: $(CMX_FILES) $(AUTOGEN)
	ocamlopt $(CMX_FILES) -o vaphor

depend: $(AUTOGEN_ML) $(ML_FILES)
	ocamldep $(OCAMLINCLUDES) *.mli *.ml */*.mli */*.ml > depend
clean: 
	rm -f *.cmo *.cmi *.cmx */*.cmi */*.cmo */*.cmx && \
	rm -f *.o $(AUTOGEN_ML) $(AUTOGEN_MLI) abstract depend *~
include depend

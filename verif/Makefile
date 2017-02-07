
COQFILES = CSP_Syntax.v CSP_OpSem.v While_Definitions.v Translation.v


all : coq

coq: Makefile $(COQFILES)
	coqc $(COQFILES)

clean :
	rm -f *.vo *~ *.glob


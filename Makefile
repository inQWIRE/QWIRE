# Using the example at https://coq.inria.fr/refman/practical-tools/utilities.html#reusing-extending-the-generated-makefile

KNOWNTARGETS := CoqMakefile all qasm

KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	git submodule init
	git submodule update
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

###########################################################
##		      Your targets here			 ##
###########################################################

COQ_OPTS := -R . Top

all: invoke-coqmakefile HOASProofs.vo Equations.vo Deutsch.vo Arithmetic.vo GHZ.vo
qasm: invoke-coqmakefile QASMExamples.vo

# Built by "make all"

HOASProofs.vo: HOASProofs.v HOASExamples.vo SemanticLib.vo
	coqc $(COQ_OPTS) HOASProofs.v

Equations.vo: Equations.v SemanticLib.vo
	coqc $(COQ_OPTS) Equations.v

Arithmetic.vo: Arithmetic.v Oracles.vo
	coqc $(COQ_OPTS) Arithmetic.v

Deutsch.vo: Deutsch.v HOASExamples.vo Denotation.vo DBCircuits.vo TypeChecking.vo
	coqc $(COQ_OPTS) Deutsch.v

GHZ.vo: GHZ.v HOASLib.vo Composition.vo
	coqc $(COQ_OPTS) GHZ.v

# Not built at all

QASM.vo : QASM.v DBCircuits.vo HOASExamples.vo
	coqc $(COQ_OPTS) QASM.v

QASMPrinter.vo : QASMPrinter.v QASM.vo
	coqc $(COQ_OPTS) QASMPrinter.v

QASMExamples.vo : QASMExamples.v QASMPrinter.vo Arithmetic.vo
	coqc $(COQ_OPTS) QASMExamples.v

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true

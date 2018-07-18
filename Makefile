all: Oracles.vo

everything: HOASProofs.vo Equations.vo Deutsch.vo Arithmetic.vo

Monad.vo: Monad.v
	coqc Monad.v

Prelim.vo: Prelim.v Monad.vo
	coqc Prelim.v

Complex.vo: Complex.v Prelim.vo
	coqc Complex.v

Matrix.vo: Matrix.v Complex.vo 
	coqc Matrix.v 

Quantum.vo: Quantum.v Matrix.vo
	coqc Quantum.v

Contexts.vo: Contexts.v Prelim.vo
	coqc Contexts.v 

HOASCircuits.vo: HOASCircuits.v Contexts.vo
	coqc HOASCircuits.v

DBCircuits.vo : DBCircuits.v HOASCircuits.vo Monad.vo
	coqc DBCircuits.v

TypeChecking.vo: TypeChecking.v HOASCircuits.vo
	coqc TypeChecking.v

HOASLib.vo: HOASLib.v TypeChecking.vo
	coqc HOASLib.v

Denotation.vo: Denotation.v Quantum.vo DBCircuits.vo HOASLib.vo
	coqc Denotation.v

Ancilla.vo : Ancilla.v Denotation.vo TypeChecking.vo
	coqc Ancilla.v

SemanticLib.vo : SemanticLib.v Ancilla.vo 
	coqc SemanticLib.v

HOASExamples.vo: HOASExamples.v HOASLib.vo
	coqc HOASExamples.v

Symmetric.vo : Symmetric.v Ancilla.vo SemanticLib.vo
	coqc Symmetric.v

Oracles.vo: Oracles.v Symmetric.vo HOASExamples.vo 
	coqc Oracles.v

# Built by "make everything"

Arithmetic.vo: Arithmetic.v Oracles.vo
	coqc Arithmetic.v

HOASProofs.vo: HOASProofs.v HOASExamples.vo SemanticLib.vo
	coqc HOASProofs.v

Deutsch.vo: Deutsch.v HOASExamples.vo Complex.vo Denotation.vo DBCircuits.vo TypeChecking.vo
	coqc Deutsch.v

Equations.vo: Equations.v SemanticLib.vo
	coqc Equations.v

# Not built at all

FlatCircuits.vo: FlatCircuits.v HOASCircuits.vo Monad.vo
	coqc FlatCircuits.v

#MachineProofs.vo: MachineProofs.v MachineExamples.vo Denotation.vo
#	coqc MachineProofs.v

#MachineCircuits.vo : MachineCircuits.v Contexts.vo FlatCircuits.vo HOASCircuits.vo Denotation.vo
#	coqc MachineCircuits.v

#MachineExamples.vo: MachineExamples.v MachineCircuits.vo
#	coqc MachineExamples

#FlatProofs.vo: FlatProofs.v FlatExamples.vo Denotation.vo
#	coqc FlatProofs.v

clean:
	rm *.vo


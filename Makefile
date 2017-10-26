all: HOASProofs.vo FlatProofs.vo MachineProofs.vo 

MachineProofs.vo: MachineProofs.v MachineExamples.vo Denotation.vo
	coqc MachineProofs.v

MachineCircuits.vo : MachineCircuits.v Contexts.vo FlatCircuits.vo HOASCircuits.vo Denotation.vo
	coqc MachineCircuits.v

DBCircuits.vo : DBCircuits.v Contexts.vo HOASCircuits.vo Monad.vo
	coqc DBCircuits.v

MachineExamples.vo: MachineExamples.v MachineCircuits.vo
	coqc MachineExamples

FlatProofs.vo: FlatProofs.v FlatExamples.vo Denotation.vo
	coqc FlatProofs.v

HOASProofs.vo: HOASProofs.v HOASExamples.vo Denotation.vo
	coqc HOASProofs.v

FlatExamples.vo: FlatExamples.v FlatCircuits.vo
	coqc FlatExamples.v

HOASExamples.vo: HOASExamples.v HOASCircuits.vo
	coqc HOASExamples.v

Denotation.vo: Denotation.v Quantum.vo HOASCircuits.vo FlatCircuits.vo
	coqc Denotation.v

FlatCircuits.vo: FlatCircuits.v HOASCircuits.vo Monad.vo
	coqc FlatCircuits.v

Monad.vo: Monad.v
	coqc Monad.v

HOASCircuits.vo: HOASCircuits.v Contexts.vo
	coqc HOASCircuits.v

Contexts.vo: Contexts.v
	coqc Contexts.v 

Quantum.vo: Quantum.v Matrix.vo
	coqc Quantum.v

Matrix.vo: Matrix.v Complex.vo
	coqc Matrix.v 

Complex.vo: Complex.v
	coqc Complex.v

clean:
	rm *.vo

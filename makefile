all: Denotation.vo UDenotation.vo

UDenotation.vo: UDenotation.v UQuantum.vo MachineExamples.vo
	coqc UDenotation.v

UQuantum.vo: UQuantum.v UMatrix.vo
	coqc UQuantum.v

UMatrix.vo: UMatrix.v
	coqc UMatrix.v 

MachineExamples.vo: MachineExamples.v MachineCircuits.vo
	coqc MachineExamples.v

MachineCircuits.vo : MachineCircuits.v Contexts.vo FlatCircuits.vo TypedCircuits.vo
	coqc MachineCircuits.v


Denotation.vo: Denotation.v Quantum.vo Examples.vo FlatCircuits.vo
	coqc Denotation.v

Quantum.vo: Quantum.v Matrix.vo
	coqc Quantum.v

Matrix.vo: Matrix.v
	coqc Matrix.v 


Examples.vo: Examples.v TypedCircuits.vo
	coqc Examples.v

FlatCircuits.vo: FlatCircuits.v TypedCircuits.vo
	coqc FlatCircuits.v

TypedCircuits.vo: TypedCircuits.v Contexts.vo
	coqc TypedCircuits.v

Contexts.vo: Contexts.v
	coqc Contexts.v 

clean:
	rm *.vo

# QWIRE

This is a Coq implementation of the QWIRE programming language described
in [QWIRE: a core language for quantum circuits][1].

Compatible with Coq 8.5 and 8.6.

This version of the project has no dependencies. Run `make` to compile the project.

Files in this repository
------------------------

*Underlying mathematical libraries*
- Complex.v : Complex number library, modified from [Coquelicot][2]
- Matrix.v : Matrix library
- Quantum.v : Defines unitary matrices and quantum operations

*Implementation of QWIRE*
- Contexts.v : Defines wire types and typing contexts
- HOASCircuits.v : Defines QWIRE circuits using higher-order abstract syntax
- HOASExamples.v : Examples using HOAS circuits
- FlatCircuits.v : Defines QWIRE circuits using an explicit representation of variable binding
- FlatExamples.v : Examples using flat circuits
- Denotation.v : Defines denotational semantics of QWIRE circuits and proves correctness of example circuits
	  
*QASM-like representation of QWIRE*
- MachineCircuits.v : Defines QWIRE circuits in the style of QASM
- MachineExamples.v : Examples using machine circuits



[1]: http://dl.acm.org/citation.cfm?id=3009894
[2]: http://coquelicot.saclay.inria.fr/html/Coquelicot.Complex.html
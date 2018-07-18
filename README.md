# QWIRE

This is a Coq implementation of the QWIRE programming language described
in [QWIRE: a core language for quantum circuits][1].

Further details on QWIRE and its implementation can be found in [2-4].
A categorical semantics for QWIRE is given in [5].

Compatible with Coq 8.5 and 8.6.

This version of the project has no dependencies. Run `make` to compile the main (implementation) files and `make everything` to compile the whole project.


Files in this repository
------------------------

*Preliminaries*
- Monad.v : An implementation of some basic monads
- Prelim.v : A variety of general purpose definitions and tactics.

*Underlying mathematical libraries*
- Complex.v : Complex number library, modified from [Coquelicot][6]
- Matrix.v : Matrix library
- Quantum.v : Defines unitary matrices and quantum operations

*Implementation of QWIRE*
- Contexts.v : Defines wire types and typing contexts
- HOASCircuits.v : Defines QWIRE circuits using higher-order abstract syntax
- DBCircuits.v : Compiling HOAS to De Bruijin style circuits
- TypeChecking.v : Circuit notations and tactics for proving well-typedness
- Denotation.v : Defines the denotational semantics of QWIRE circuits and proves its (quantum mechanical) validity
- HOASLib.v : A library of basic circuits used in QWIRE programming
- SemanticLib.v : Proves the semantic properties of HOASLib circuits.
- Ancilla.v : Defines the correctness of circuits using ancilla assertions
- Symmetric.v : Syntactic conditions for guaranteeing the validity of assertions
- Oracles.v : Compilation of boolean expressions to QWIRE circuits
- HOASExamples.v : Additional examples of HOAS circuits

*Verification of QWIRE circuits*
Arithmetic.v : Verification of a quantum adder
Deutsch.v : Verification of Deutsch's Algorithm
Equations.v : Equalities on small circuits
HOASProofs.v : Additional proofs, including coin flips and teleportation

*Compilation to QASM[7]*
- QASM.v : Compilation from QWIRE to QASM
- QASMExamples.v : Examples of circuit compilation
- QASMPrinter.v : A printer for compiled circuits, for execution on a quantum computer/simulator


[1]: http://dl.acm.org/citation.cfm?id=3009894
[2]: http://www.cis.upenn.edu/~rrand/qpl_2017.pdf
[3]: http://www.cis.upenn.edu/~rrand/qpl_2018.pdf
[4]: http://www.cis.upenn.edu/~rrand/coqpl_2018.pdf
[5]: https://arxiv.org/pdf/1711.05159.pdf
[6]: http://coquelicot.saclay.inria.fr/html/Coquelicot.Complex.html
[7]: https://developer.ibm.com/code/open/projects/qiskit/qiskit-openqasm/
# QWIRE

This is a Coq implementation of the QWIRE quantum programming language, described in the following papers by Jennifer Paykin, Robert Rand, Dong-Ho Lee and Steve Zdancewic:
- [QWIRE: a core language for quantum circuits][1].
- [QWIRE Practice: Formal Verification of Quantum Circuits in Coq][2]
- [ReQWIRE: Reasoning about Reversible Quantum Circuits][3]
- [Phantom Types for Quantum Programs][4]

Rennela and Staton's [Classical Control, Quantum Circuits and Linear Logic in Enriched Category Theory][5] provides a categorical semantics for QWIRE.

QWIRE is compatible with Coq versions 8.12 - 8.15.

This project depends on [QuantumLib](https://github.com/inQWIRE/QuantumLib), which you can install with: 
```
opam pin coq-quantumlib https://github.com/inQWIRE/QuantumLib.git
```
Run `make` to compile the core (preliminary and implementation) files and `make all` to compile proofs of QWIRE programs. Run `make qasm` to compile the files that convert QWIRE to QASM. We recommend using [Company Coq][9] with QWIRE in light of its support for unicode.  


Files in this repository
------------------------

*Preliminaries*
- Monad.v : An implementation of some basic monads
- Monoid.v : A typeclass and solver for commutative monoids, modified from [LinearTypingContexts][8]

*Implementation of QWIRE*
- Contexts.v : Defines wire types and typing contexts
- HOASCircuits.v : Defines QWIRE circuits using higher-order abstract syntax
- DBCircuits.v : Compiling HOAS to De Bruijin style circuits
- TypeChecking.v : Circuit notations and tactics for proving well-typedness
- Denotation.v : Defines the denotational semantics of QWIRE circuits and proves its (quantum mechanical) validity
- HOASLib.v : A library of basic circuits used in QWIRE programming
- SemanticLib.v : Proves the semantic properties of HOASLib circuits
- HOASExamples.v : Additional examples of HOAS circuits
- Composition.v : States and admits compositionality lemmas (used in the following five files)
- Ancilla.v : Defines the correctness of circuits using ancilla assertions
- Symmetric.v : Syntactic conditions for guaranteeing the validity of assertions
- Oracles.v : Compilation of boolean expressions to QWIRE circuits

*Verification of QWIRE circuits*
- Arithmetic.v : Verification of a quantum adder
- Deutsch.v : Variants on Deutsch's Algorithm
- Equations.v : Equalities on small circuits
- HOASProofs.v : Additional proofs, including coin flips and teleportation

*Compilation to [QASM][7] (i.e., OpenQASM 2.0)*
- QASM.v : Compilation from QWIRE to QASM
- QASMPrinter.v : A printer for compiled circuits, for execution on a quantum computer/simulator
- QASMExamples.v : Examples of circuit compilation


*The QWIRE project has benefited from the support of the Air Force Office of Scientific Research under the MURI grant number FA9550-16-1-0082 entitled, “Semantics, Formal Reasoning, and Tool Support for Quantum Programming” and the U.S. Department of Energy, Office of Science, Office of Advanced Scientific Computing Research, Quantum Testbed Pathfinder Program under Award Number DE-SC0019040.*



[1]: http://dl.acm.org/citation.cfm?id=3009894
[2]: https://doi.org/10.4204/EPTCS.266.8
[3]: https://doi.org/10.4204/EPTCS.287.17
[4]: https://rand.cs.uchicago.edu/files/coqpl_2018.pdf
[5]: https://arxiv.org/pdf/1711.05159.pdf
[6]: http://coquelicot.saclay.inria.fr/html/Coquelicot.Complex.html
[7]: https://arxiv.org/abs/1707.03429
[8]: https://github.com/inQWIRE/LinearTypingContexts
[9]: https://github.com/cpitclaudel/company-coq

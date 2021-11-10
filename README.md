# Hamiltonian Simulation Formulation

This document is taken from the initial discussion notes and is really unpolished. Also, obviously work-in-progress.

We will implement Hamiltonian simulation in Coq.

We will implement the syntax. We then either prove some basic facts on its semantics, or implement compilation to quantum circuit. Or possibly both if time permits.

## What is Hamiltonian simulation?

TODO Maybe say something about Schrödinger's equation and its solution?

## Relevant works

Notable work on formally verified quantum computing using Coq has been done before, notably in [this library](https://rand.cs.uchicago.edu/vqc/) by Robert Rand, [SQIR/VOQC](https://github.com/inQWIRE/SQIR), and [QWIRE](https://github.com/inQWIRE/QWIRE). The first library implements the basics of quantum computation including qubits, measurements, and small quantum circuits and the latter three libraries implement many more advanced features. We expect `matrix.v` in QWIRE to be especially helpful as it proves many linear algebra fundamentals.

To the best of our knowledge, formal verification of Hamiltonian simulation semantics is new. Our main contribution will be to prove theorems on the semantics of both commuting and non-commuting Hamiltonians, which will involve formulating a Coq representaion of the exponentiation of a matrix.

## Syntax

The formal grammar is provided below. We will implement it using a similar strategy as how the `Imp` language from the Software Foundation textbook is defined and parsed.

### Formal grammar

* `A`: identifier
* `z`: complex number
* `r`: real number
* `t`: positive real number.

<pre><code>Type := <b>qubit</b> | <b>fock</b>
Operator := Id | X | Y | Z | a | c
Declaration := (T A)*
Scalar := S_1 + S_2 | S_1 * S_2 | S_1 - S_2 | S_1 / S_2 | exp(S) | cos(S) | sin(S) | z | r
TIH := M_1 + M_2 | M_1 * M_2 | S * M | A.O
TIH_Sequence := (A : t, M)*
Program := <b>Site</b> Declaration; <b>Hamiltonian</b> TIH_Sequence
</code></pre>

### Example

The following is a valid Hamiltonian simulation program:

```
Site
    fock "F1"
    qubit "Q1"
    qubit "Q2"
    qubit "Q3" ;
Hamiltonian
    ( "H1" : R1 , "Q1" > X * "Q2" > Z + "Q3" > Y )
    ( "H2" : R1 , "Q2" > Y )
    ( "H3" : R1 , "F1" > c )
)
```

In the first *Site* section, four variables are declared. We have `F1` of type fock, as well as `Q1`, `Q2`, and `Q3` of type qubit.
We then describe the desired evolution in the *Hamiltonian* section.
Namely, we have three Hamiltonians, `H1`, `H2`, and `H3`, applied in that order for one unit of time each.

The corresponding quantities are <!-- google charts LaTeX workaround; you hate to see it -->
* ![H1](http://chart.apis.google.com/chart?cht=tx&chl=H_1=\mathsf{I}{\otimes}\mathsf{X}{\otimes}\mathsf{Z}{\otimes}\mathsf{I}%2B\mathsf{I}{\otimes}\mathsf{I}{\otimes}\mathsf{I}{\otimes}\mathsf{Y})
* ![H2](http://chart.apis.google.com/chart?cht=tx&chl=H_2=\mathsf{I}{\otimes}\mathsf{I}{\otimes}\mathsf{Y}{\otimes}\mathsf{I})
* ![H3](http://chart.apis.google.com/chart?cht=tx&chl=H_3=c{\otimes}\mathsf{I}{\otimes}\mathsf{I}{\otimes}\mathsf{I})

## Project Goals

### Semantics

We aim to prove when different Hamiltonians have the same semantics, that is, when they have the same effect on any given state.
In particular, if `H_1` and `H_2` commute, then `(H_1: t_1) (H_2, t_2)` and `(H_2: t_2) (H_1, t_1)` have the same semantics.

One challenge will be representing matrix exponentials. We plan to define this symbolically (since the formal definition requires an infinite sum) and state valid rewrite rules that respect Schrödinger's equation.

### Compilation

Another goal of this project is to implement and prove facts about Hamiltonian compilation. Given some universal gate set `G` and a Hamiltonian `H`, this involves constructing a program `P : list G` such that `P` and `H` have the same effect on a quantum state.

The method of compilation will be via *trotterization*. Trotterization decomposes the unitary induced by a Hamiltonian into a product of local terms. 
We can then analyze its properties by, for example, proving the error bound on trotterization for non-commuting Hamiltonians.

If time permits, we may attempt to compile the Hamiltonian into a popular quantum programming language such as [OpenQASM](https://github.com/Qiskit/openqasm),
so that it can be run on a simulator or a real quantum computer.

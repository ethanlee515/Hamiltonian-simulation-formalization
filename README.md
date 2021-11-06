# Hamiltonian Simulation Formulation

This document is taken from the initial discussion notes and is really unpolished. Also, obviously work-in-progress.

We will implement Hamiltonian simulation in Coq.

We will implement the syntax. We then either prove some basic facts on its semantics, or implement compilation to quantum circuit. Or possibly both if time permits.

## What is Hamiltonian simulation?

TODO Maybe say something about Schrödinger's equation and its solution?

## Relevant works

TODO describe [this library](https://rand.cs.uchicago.edu/vqc/) and maybe [SQIR/VOQC](https://github.com/inQWIRE/SQIR).

TODO What exactly has been done before, and how are we adding onto existing work?

I think Dr. Wu said something about 2x2 matrices were currently brute forced? What did he mean by that? Does that matter to us?

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

### Explanations

TODO

## Semantics

Goal: Be able to prove when different Hamiltonians have the same semantics.
For example, if `H_1` and `H_2` commute, then `H_1H_2` and `H_2H_1` have the same semantics... (Isn't this trivial? Did I mishear something during the meeting?)

Challenge: matrix exponentials. Not even sure how to represent it.
We were suggested to define it symbolically and state valid rewrite rules that respect Schrödinger's equation.
Need to discuss the details though.

## Compilation

First write down the compiler using *trotterization* (TODO explain). We can then analyze its properties.
For example, how much error it generates.

Here we can just assume the gate set to be whatever convenient for us.
We can also assume the Hamiltonian is *local*.

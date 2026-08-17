---
rg: 2
id: stable-finiteness-failure-refutes-surjunctivity
kind: claim
title: A one-sided inverse over a finite field refutes surjunctivity
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

Let `k` be a finite field and `G` any group.  If for some finite `n >= 1`
there are `A, B` in `M_n(k[G])` with

    B A = I_n,        A B != I_n,

then `G` is **not surjunctive**: there is an injective non-surjective
cellular automaton on the full shift over the finite alphabet `k^n`.

At `n = 1` this is the statement that a counterexample to Kaplansky direct
finiteness over a finite field is automatically a counterexample to
Gottschalk's conjecture; the matrix form shows failure of stable finiteness
is enough as well.

The automaton produced is linear with finite memory: the entries of `A` have
finite support in `G`, and the local rule is the corresponding finite sum of
coordinates.

This is a general lemma about group algebras, with no Leavitt content.  It is
the only live bridge in this graph from algebra to
`leavitt-unit-group-nonsurjunctive`.  The relation between stable finiteness
of `k[G]` and surjunctivity of linear cellular automata is standard in that
literature (Ceccherini-Silberstein and Coornaert); the proof is carried in
full here rather than imported, so this node has no trust surface.

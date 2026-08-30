---
rg: 2
id: lcs-occurrence-two-qc-equals-q
kind: claim
title: Perfect commuting and finite-dimensional play coincide when every LCS variable occurs at most twice
distinct_from:
  high-girth-incidence-gives-uniform-quantum-classical-separation: that supplies commuting-versus-classical separation for closed graph-incidence systems over every modulus; this proves that in the binary case such systems, even after adjoining arbitrary dangling variables, never separate commuting from finite-dimensional quantum play.
  perfect-completeness-constant-soundness-lcs-compiler: that asks for a machine-indexed family separating perfect commuting play from all finite-dimensional play; this proves that every output of such a family must have a variable of occurrence at least three.
  solution-group-central-order-is-operator-solvability: that turns exact order of the central phase into an arbitrary-dimensional operator solution; this proves finite-dimensional realizability for a structural class of binary systems.
---

Let `Ax=b` be a finite binary linear constraint system.  Suppose every
column of `A` has Hamming weight at most two, or equivalently every variable
occurs in at most two equations.  Then

```text
omega^co(LCS(A,b))=1    if and only if    omega^q(LCS(A,b))=1.   (OT1)
```

More concretely, every possibly infinite-dimensional operator solution of
`Ax=b` can be replaced by a finite-dimensional operator solution (not
necessarily by compressing the given one).  In solution-group language, if
the distinguished central involution `J` is nontrivial, then there is a
finite-dimensional representation `pi` with `pi(J)=-I`; thus `J` can never
be a nontrivial finite-dimensional, hyperlinear, or MF radical mark in this
occurrence class.  Consequently no binary LCS with
variable occurrence at most two can witness

```text
omega^co=1 > omega^q,
```

and every candidate for
`perfect-completeness-constant-soundness-lcs-compiler` must contain a
variable occurring in at least three equations.

The proof decomposes the equation-variable incidence structure into graph
components with dangling half-edges.  A component with a half-edge is
classically solvable for every right-hand side.  A component without one is
a graph-incidence system.  After harmlessly merging parallel edges,
Arkhipov's theorem says that perfect commuting play for a binary graph
incidence game is equivalent to perfect finite-dimensional quantum play.
Tensoring the finitely many component strategies gives `(OT1)`.

This is a perfect-value theorem only.  It supplies no dimension-independent
rounding modulus for strategies of value `1-epsilon`.

---
rg: 2
id: finite-magic-square-selector-has-no-frozen-branch
kind: claim
title: A finite perfect ZPC magic-square selector has no consistent frozen readable branch
distinct_from:
  zpc-frozen-equation-menu-has-positive-orbitwise-class: that asks for a specially selected perfect-gap TailoredMIP witness; this is a finite perfect ZPC counterexample to deriving orbitwise freezing from the structural axioms alone.
  scalar-relator-compression-does-not-kill-normal-ideal: that gives a two-dimensional ucp counterexample for one relator; this realizes the same normal-orbit obstruction inside an ordinary finite LCS packet and defeats every readable branch.
---

**ESTABLISHED FINITE COUNTEREXAMPLE.**  There is a finite tailored
controlled-linear game `H_ms` with one readable bit `r` such that:

1. `H_ms` has a perfect finite ZPC permutation strategy;
2. for each frozen value `epsilon in F_2` of `r`, the associated ordinary
   linear system has `J=1` in its solution group, and hence has no perfect
   commuting-operator strategy in the negative central sector.

Use the standard Mermin--Peres magic-square linear system with unreadable
involutions `x_ij`, `1<=i,j<=3`.  Rows and columns commute, the three row
products and first two column products are `1`, and the last column product
is `J`.  In its solution group,

```text
[x_11,x_22]=J.                                           (MSS1)
```

Add one readable bit `r` and one controlled singleton equation

```text
x_22=J^r.                                                 (MSS2)
```

The usual real two-qubit Pauli magic-square representation is signed
monomial.  Take `x_22=Z tensor I`, let the readable variable act by that same
signed permutation, and let `J=-I`.  The readable action is Z-aligned: on
each signed pair it is either the identity or the sign flip.  It commutes
with `x_22`, and it is not required to commute with the remote variable
`x_11=X tensor I`.  Thus all magic-square rows and `(MSS2)` are satisfied
perfectly by a finite ZPC permutation strategy.

After freezing `r=epsilon`, `(MSS2)` makes `x_22` equal to the central scalar
`J^epsilon`.  Its commutator with `x_11` is therefore `1`, while `(MSS1)`
makes the same commutator equal to `J`.  Hence `J=1` in either frozen
solution group.  Both branches are operator-inconsistent in the required
`J=-1` sector.

The direct calculation and the signed-action realization are in
`finite-magic-square-selector-no-freezing-proof`.

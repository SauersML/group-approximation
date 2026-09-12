---
rg: 2
id: doubling-tape-from-self-similar-quantum-expander
kind: route
title: Use quantum expansion to exactify one new Clifford cell uniformly along the tape
target: uniform-relative-clifford-tape-cell
requires:
  - self-similar-clifford-quantum-expander-tape
  - quantum-expander-rounds-relative-pauli-cell
---

At level `n`, use the expander words to move the proposed new controlled Pauli
cell uniformly close to the commutant of the exactified `E_n` spin factor.
The relative-cell theorem exactifies only its fixed `D_8` table, with constants
independent of `n`, and its correcting isometry is tensored with the identity
on the old spin factor. This gives the claimed one-step relative
exactification.

The remaining passage from these one-step corrections to
`finite-dimensional-schur-lift-of-doubling-tape` still requires coherent
sequential composition and payment for selector sectors which do not activate
the rank jump.

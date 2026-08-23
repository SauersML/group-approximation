---
rg: 2
id: goldbring-sinclair-max-u-trace-blind-proof
kind: route
title: Rewrite the max-U algebra as a sofic full group algebra and separate its regular and quotient traces
target: goldbring-sinclair-max-u-group-witness-is-trace-blind
requires:
  - non-ce-property-t-equivalence-relation-exists
  - nonce-factor-in-group-factor-corner-forces-nonhyperlinear
---

Goldbring--Sinclair Theorem 3.23 starts with any countable `G` for which
`C^*(G)` fails LP.  Choose `G=SL_3(Z)` using Ioana--Spaas--Wiersma
Corollary B (LLP fails, hence LP fails).  The finite product `D_J=D^m` is
the full group C-star algebra of `(F_infinity*G) x C_m`, and unital full
C-star free products are full group C-star algebras of group free products.
This gives the displayed `Gamma` and imports the source theorem's failure of
property `max-U`.

Residual finiteness of `SL_3(Z)` and standard sofic closure under direct
products, free products, and directed unions make `Gamma` sofic.  Hence its
regular trace is CE.

For the non-CE trace, take a norm-separable unital unitary-generating C-star
subalgebra which is strongly dense in the non-CE II1 factor supplied by the
first prerequisite.  Surjective universality of `C^*(F_infinity)` gives a
quotient of `C^*(Gamma)` onto that algebra.  Pullback preserves the GNS von
Neumann algebra and hence produces a non-CE factorial trace on
`C^*(Gamma)`.

The last prerequisite says that an embedding of this factor into a nonzero
corner of `L(Gamma)` would force `Gamma` nonhyperlinear.  Since the already
proved soficity makes `Gamma` hyperlinear, no such embedding exists.  More
directly, CE passes from `L(Gamma)` to its corners and von Neumann
subalgebras.  This proves every clause.

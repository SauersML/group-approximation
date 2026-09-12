---
rg: 2
id: monomial-projective-color-rigidity-proof
kind: route
title: Quotient the scalar entry labels by the common root-of-unity action
target: monomial-game-pair-compatibility-is-projective-color-rigid
requires:
  - finite-phase-monomial-game-algebra-dictionary
---

If `A_(ij)=0`, equation `(MCR2)` holds precisely when `B_(kl)=0`.  If both
entries are nonzero, `(MCR2)` is equivalent to

```text
A_(ij)=(b/a)B_(kl),          b/a in mu_s,
```

which is equality of their projective colors.  A source pair therefore sees
exactly one target color class, proving the identical-or-disjoint assertion.
For finitely many intertwining matrices the same ratio `b/a` must multiply
the entire entry vector, so compatibility is equality of vector orbits under
the common `mu_s` action.


---
rg: 2
id: radial-finite-solvable-quotient-proof
kind: route
title: Split a minimal solvable quotient and connect each negative sign support
target: radial-simplex-has-no-nonabelian-finite-solvable-quotient
requires:
  - radial-parallelograms-kill-simplex-class-two
  - affine-sign-support-is-radially-connected
---

Choose a minimal nonabelian solvable quotient and its minimal normal module
`A`.  Minimality gives `A=G'` and makes it an irreducible module over the
elementary abelian 2-group `G/A`.  Characteristic two reduces to the already
closed class-two case.  In odd characteristic the module is one sign line
and Schur--Zassenhaus gives coordinates `(v_x,h_x)`.

The order-two and local commutation equations are exactly `(RSQ3)` and
equality of `v_x` on every negative co-occurring pair.  Radial connectivity
makes this one global scalar, which is a coboundary because two is invertible.
All coordinate lifts lie in one conjugate complement, contradicting
nonabelian generation.

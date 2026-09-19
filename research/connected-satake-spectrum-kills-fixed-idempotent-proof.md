---
rg: 2
id: connected-satake-spectrum-kills-fixed-idempotent-proof
kind: route
title: Use connectedness and full Plancherel support of the tempered Satake quotient
target: fixed-spherical-polynomials-have-no-42nd-projection
requires:
  - finite-spherical-moments-do-not-fold-regular-double
---

# Use connectedness and full Plancherel support of the tempered Satake quotient

The maximal compact Satake torus is connected, and its quotient by the finite
Weyl group is connected.  The spherical Plancherel transform has full support
on that quotient.  Therefore a continuous Hecke transform satisfying
`f^2=f` in Plancherel `L^2` satisfies it everywhere and is a continuous map
from a connected space to `{0,1}`.  It is constant, proving `(FSP4)`.

For a fixed polynomial, the squared idempotence and self-adjointness defects
are finite linear combinations of regular word moments.  Canonical
microstate convergence transports `(FSP5)` to `(FSP6)`, so the same argument
proves the matrix formulation.  The existing finite-moment quadrature theorem
gives the final authentication fence.

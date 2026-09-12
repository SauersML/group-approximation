---
rg: 2
id: fournier-facio-map-from-asymptotic-triviality-proof
kind: route
title: Regard an exact finite-dimensional representation as a constant asymptotic representation
target: fournier-facio-group-is-minimally-almost-periodic
requires:
  - fournier-facio-asymptotic-representations-trivial
  - fournier-facio-torsion-free-skeleton
---

Let `rho:G -> U(d)` be an exact finite-dimensional representation and take
the constant operator-norm asymptotic representation `phi_n=rho`.  The
established total-corona-triviality theorem gives, for every `g in G`,

```text
||rho(g)-1|| = ||phi_n(g)-1|| -> 0.
```

The left-hand side is constant, hence zero.  Thus `rho(g)=1` for every `g`.
The skeleton contains an injective copy of the nontrivial simple group `S`,
so `G` itself is nontrivial and the usual minimally-almost-periodic
terminology applies.


---
rg: 2
id: isotypic-selector-support-proof
kind: route
title: Decompose induction through the commuting selector extension
target: isotypic-finite-edge-forces-full-commuting-selector-support
requires: []
---

Put `L=HA`.  Schur's lemma gives the character of `A intersect H` on the
chosen `H`-type `sigma`.  Every extending character `chi` defines
`sigma tensor chi` on `L`, and Fourier decomposition gives

```text
Ind_H^L(sigma)=directSum_chi sigma tensor chi.
```

Functions supported on `L` embed this representation in the restriction of
`Ind_H^G(sigma)`.  If the latter is isotypic of type `rho`, every displayed
summand occurs in `rho|_L`; restricting to `A` yields every compatible
character.  The central-idempotent/source-Gram formulation is equivalent by
the usual decomposition of the regular representation.

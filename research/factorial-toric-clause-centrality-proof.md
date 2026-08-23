---
rg: 2
id: factorial-toric-clause-centrality-proof
kind: route
title: Centralize every clause component in the full trace and apply it to the monomial Fourier generators
target: toric-clause-spectra-cannot-generate-monomial-factor
requires:
  - finite-phase-monomial-game-algebra-dictionary
  - toric-gap-is-a-relative-fd-central-word-face
---

In the faithful trace GNS image, a zero-`2`-norm clause is the operator
identity

```text
beta_t rho_A(a_t)rho_B(b_t)=1.
```

The player images commute, so rearranging places `rho_A(a_t)` simultaneously
in `M_A` and `M_A'`, and likewise on Bob's side.  This proves `(MTC2)`.

The finite-phase dictionary gives `(MTC3)` and the inverse formula
`u_(ki)=sum_p zeta^p e_(ki)^p`, so the Fourier projections generate the
monomial algebra.  If a proposed full corner puts them in the spectral
algebra of the central clause components, the corner is commutative.
An extreme trace on the nonempty tracial state space is factorial.  The
assumption that the monomial algebra has no nonzero map to `R^omega` excludes
the one-dimensional factor, giving the contradiction.

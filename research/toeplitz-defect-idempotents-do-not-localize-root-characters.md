---
rg: 2
id: toeplitz-defect-idempotents-do-not-localize-root-characters
kind: claim
title: Orthogonal Toeplitz defects do not give disjoint additive-root character layers
distinct_from:
  triangular-e5-pulses-admit-persistent-tail-character: that recursively follows triangular polynomial pulses; this uses the literal pairwise-orthogonal Toeplitz idempotents and shows that even orthogonality does not constrain additive characters.
  free-root-top-boundary-reservoir-is-summable: that correctly sums spectral first-hit projections; this proves coefficient idempotents alone do not make root-character detection a first-hit decomposition.
---

In the ring `R_f` of `schur-idempotent-is-an-injective-toeplitz-defect`, put

```text
e_n=x^nP_fy^n,                  n>=0.                       (TDC1)
```

The `e_n` are nonzero pairwise orthogonal idempotents and therefore linearly
independent over the coefficient field `k`. Nevertheless, for every `N`
there is an additive character

```text
chi:(R_f,+)->mu_p
```

such that `chi(e_n)!=1` for all `0<=n<N`; there is also a character with this
property for every `n>=0` simultaneously.

Choose a linear functional `ell:R_f->F_p` taking value one on every `e_n`,
extend it from their linear span to the whole vector space, and put
`chi(a)=exp(2 pi i ell(a)/p)`. Thus a joint eigenvector for an additive root
subgroup may detect all Toeplitz boundary coefficients while belonging to
one and the same root-character fiber.

Consequently coefficient orthogonality alone does not make the masses of
`x_ij(e_n)` summable. A valid first-hit proof must use multiplicative
Steinberg partners, a lower-root triviality condition, or contextual Schur
branching; it cannot infer spectral disjointness from `e_ne_m=0`.

---
rg: 2
id: exact-expander-a5-mark-collapse-proof
kind: route
title: Project the finite center label to Gamma invariants and use finite-image compression collapse
target: exact-expander-a5-carriers-collapse-marked-center
requires:
  - finite-quotient-blindness
  - two-site-a5-plancherel-center-separates-mark
  - exact-models-cannot-separate-marked-pair
---

Put `f=1_E in ell^2(Y)` and let `P` be the orthogonal projection onto the
`phi(Gamma)`-invariant vectors.  The Kazhdan inequality and `(AEC2)` give

```text
||f-Pf||_2 <= sqrt(delta)/kappa.                         (AEC7)
```

In every finite image the subgroup `phi(Gamma)` is normal.  The pinned
compressor is conjugate in `G` to an element of `Gamma`; hence
`phi(h) in phi(Gamma)`.  It follows that `phi(h)Pf=Pf`, and therefore

```text
||phi(h)f-f||_2
 <= ||phi(h)(f-Pf)||_2+||f-Pf||_2
 <= 2 sqrt(delta)/kappa.                                (AEC8)
```

The square of the left side is the normalized symmetric-difference mass,
which proves `(AEC3)`.  For `(AEC5)`, apply the triangle inequality to
`1_(E_q)-1_(E_p)` through `phi(h)1_(E_p)` and use `(AEC4)` and `(AEC8)`.
Finally `(AEC6)` is the exact Plancherel calculation from
`two-site-a5-plancherel-center-separates-mark`.


---
rg: 2
id: a4-holonomy-gap-from-four-cycle-dirichlet
kind: route
title: One vanishing four-cycle Dirichlet energy collapses the relative A8 frame
target: atlas-a4-holonomy-coherence-gap
requires:
  - atlas-a4-four-cycle-dirichlet-compiler
  - atlas-a8-four-cycle-commutant-gap
---

Let

```text
E_n=sum_(t in {t01,t12,t23,t30}) (1-Re tau_n(V_n(t))).
```

By `(A4-DIR)` and the normalized-network hypotheses, `E_n->0`.  For every
cycle transvection,

```text
||[U_n,lambda_(k_n)(t)]||_2^2
 = ||V_n(t)-1||_2^2
 = 2(1-Re tau_n(V_n(t))),
```

so the sum of the four squared commutator defects is `2E_n->0`.
`atlas-a8-four-cycle-commutant-gap` now gives

```text
dist_2(U_n,lambda_(k_n)(A8)') ->0.
```

Choose `Y_n` in the right-regular commutant with `||U_n-Y_n||_2->0`.  The two
fixed raw-S3 involutions `h_a,h_b` belong to the A8 chart, hence for either
`h`,

```text
||[U_n,lambda_(k_n)(h)]||_2
 <= 2||U_n-Y_n||_2 ->0.
```

Thus the two covariance coordinates satisfy

```text
a_n^2+b_n^2 ->0 < 1/128,
```

proving the holonomy coherence gap.  The entire direct nonhyperlinear route can
therefore be driven by one scalar finite-dimensional Poincare inequality.

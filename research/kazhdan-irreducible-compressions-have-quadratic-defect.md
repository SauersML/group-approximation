---
rg: 2
id: kazhdan-irreducible-compressions-have-quadratic-defect
kind: claim
title: Small compressions of irreducible Kazhdan representations have quadratic defect scale
artifacts:
  - research/artifacts/general-irreducible-compression-quadratic-defect-2026-09-05.md
distinct_from:
  compressed-irreducibles-require-all-deleted-dimensions: that excludes exact corrections in dimensions smaller than the original irreducible; this bounds the defining defect from below by the deleted dimension fraction for all small deletion ratios.
  kazhdan-approximate-coefficients-have-curved-hodge-control: that controls arbitrary supplied coefficient heat flows; this applies it to a compressed irreducible and uses Schur variance to quantify its unavoidable defect.
---

Let G=<S|R> be a fixed finitely presented Kazhdan group, with inverse
labels and cochain consistency as in the curved Hodge theorem. There
are theta_0,c,C>0 such that for every irreducible rho:G->U(N), every
removed k-dimensional subspace with `0<k/(N-k)<=theta_0`, and every
inverse-compatible unitary polar completion U of the compressed
generators, its maximum normalized-HS defining defect delta satisfies

```text
c k/(N-k) <= delta^2 <= C k/(N-k).                     (KIC1)
```

No H2 vanishing or finite-image hypothesis is required. The constants
depend only on the fixed presentation and Kazhdan data. In particular,
for any sequence k=o(N) with k>0, `d delta^2` is comparable to k,
where d=N-k. This includes growing k, not only one-dimensional cuts.

Let W:C^d->C^N be the inclusion. At sufficiently small positive delta,
its coefficient heat flow produces, at time O(log(1/delta)), an operator
contraction A with

```text
||A||HS^2 >= d/2,
sum_s||rho(s)A-AU_s||HS^2 <= B delta^2 d.              (KIC2)
```

Irreducible Schur variance of AA* then detects every missing dimension.
The Rayleigh quotient of this map for the coefficient connection
Laplacian is at most `(2B/h)delta^2`, where h=|S|. The supplied
irreducible exact ambient is essential to this proof.

DERIVATION
contractive-heat-and-schur-variance-compression-proof

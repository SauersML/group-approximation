---
rg: 2
id: thompson-action-on-odd-measures-is-essentially-free
kind: claim
title: Thompson's group V acts essentially freely on the odd F_2-measures with their Haar measure
distinct_from:
  odd-measure-space-has-no-honest-thompson-compression: that uses only V-invariance of Haar measure to forbid honest clopen compressions; this shows every nontrivial element of V has a Haar-null fixed set on M_-, so almost every orbit is a copy of V.
artifacts:
  - research/artifacts/odd-measure-star-compression-designs-2026-09-12.md
---

Let `M_-` be the space of finitely additive `F_2`-valued measures `mu` on the clopens of Cantor space
`X` with `mu(X) = 1`, and `lambda` its normalized Haar measure (the restriction of Haar measure on
`M = Hom(C(X, F_2), F_2)` to this index-two coset). Thompson's group `V` acts by
`(g mu)(C) = mu(g^-1 C)`.

For every `g != 1` in `V`, the fixed set `{mu in M_- : g mu = mu}` is `lambda`-null. So `V` acts
essentially freely on `(M_-, lambda)`.

Proof: `Fix(g)` lies in the annihilator of `D_g = {f o g + f}`, which is infinite-dimensional because
`g` moves a cylinder `C` off `g^-1 C` and the subcylinders of `C` give independent vectors. The
annihilator of an infinite-dimensional subspace is Haar-null. Section 3 of the artifact, route
`thompson-action-on-odd-measures-essentially-free-proof`.

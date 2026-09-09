---
rg: 2
id: locally-residually-finite-targets-kill-compression-defects-proof
kind: route
title: Equal cardinality forces the compressed image to be the whole image in every finite quotient
target: locally-residually-finite-targets-kill-compression-defects
requires: []
artifacts:
  - research/artifacts/finite-rank-compression-defect-dichotomy-2026-09-09.md
---

## Why sufficient

Fix a defining generator `d = [u c u^-1, l]` of `D_G(L)`, with
`u L u^-1 <= L`, `c in C_G(L)`, `l in L`.  The group

```text
Q_0 = < phi(L), phi(u), phi(c) >
```

is finitely generated, because `L` is, so it is residually finite by the
hypothesis on `Q`.  Let `q : Q_0 -> F` be a homomorphism to a finite
group and put `A = q phi(L)`, `v = q phi(u)`, `b = q phi(c)`.  Applying
`q phi` to `u L u^-1 <= L` gives `v A v^-1 <= A`.  Both sides are finite
sets of the same cardinality, so `v A v^-1 = A`.  Since `b` centralizes
`A`, the element `v b v^-1` centralizes `v A v^-1 = A`, and in particular
commutes with `q phi(l) in A`.  So `q phi(d) = [v b v^-1, q phi(l)] = 1`.

This holds for every finite quotient of `Q_0`, and `Q_0` is residually
finite, so `phi(d) = 1`.  The kernel of `phi` is normal in `G` and
contains every defining generator, hence contains their normal closure
`D_G(L)`.

## What is used

Only that finite sets of equal size with one contained in the other are
equal.  There is no approximation norm, no almost-invariant vector, no
transport of Kazhdan projections; this is why the theorem applies to
targets with no analytic structure at all.

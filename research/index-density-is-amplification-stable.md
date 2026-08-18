---
rg: 2
id: index-density-is-amplification-stable
kind: claim
title: The density of an additive index survives tensor amplification, unlike the index itself
distinct_from:
  additive-index-instability: that claim kills the *raw* additive index as a normalized-HS invariant, because amplification multiplies it; this observes that the same computation leaves the index-per-dimension fixed, so it locates which quantity the no-go does and does not reach
  exel-loring-relative-quasirep-invariant: that is a relative quasi-representation invariant for a specific pair; this is a scaling remark about any additive index under the one amplification that preserves all normalized-HS data
artifacts:
  - research/artifacts/universal-hyperlinearity-audit-2026-08-18.md
---

ESTABLISHED, elementary, and stated only to bound the reach of an existing
no-go.

`additive-index-instability` records that replacing a microstate `phi` by
`phi ⊗ I_k` preserves every normalized-HS defect, trace, separation and
scalar word value, while multiplying an additive Fredholm/rank index by `k`.
That is what kills determinant and parity shortcuts.  The same computation
gives, for the **density**

```text
rho(phi) = index(phi) / dim(phi),
rho(phi ⊗ I_k) = (k · index(phi)) / (k · dim(phi)) = rho(phi).
```

So the index density is an amplification invariant.  The no-go applies to the
raw index and to every quantity normalized by anything other than the
dimension; it does not reach the density.

## What this does and does not buy

It does **not** revive any route.  `additive-index-transducer` is invalidated
for reasons the density does not repair: a rank-one or bounded-rank defect has
density `O(1/n) -> 0`, which is exactly the regime normalized HS is designed
to discard, and the transducer produced a bounded defect.

What it buys is a **specification**.  If a topological or index obstruction is
ever to be visible to the normalized Hilbert--Schmidt metric, it must be
*extensive*: the number of independent defects has to grow like `Theta(n)` in
the matrix dimension, so that the density stays bounded away from zero.  This
converts "find a topological obstruction" into "force positive-density
syndrome", which is a construction problem with a literature -- see
`extensive-cosystolic-index-defect`.

The finite-rank-invisibility half of this is the standing reason the program
treats topological obstructions as peripheral; the density observation is
what leaves a door open, and it is a narrow one.

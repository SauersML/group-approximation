---
rg: 2
id: q-masa-selector-bridge-is-scale-conservation
kind: claim
title: A q-MASA-to-selector bridge converts multiplicity only by changing matrix scale
distinct_from:
  hnn-conjugacy-cannot-return-schur-morita-multiplicity: that treats conjugacy between two finite subgroup representations abstractly; this computes the apparent gain in the concrete q-MASA reset and shows it is exactly inverse to the fresh packet's irreducible dimension.
  full-q-masa-forgets-selectors-retains-branches: that proves the complete character vector still distinguishes the two children; this proves ordinary selector extension cannot convert that distinction into fixed-scale contraction.
---

Let a finite packet representation restrict to the elementary abelian
`q`-MASA `K`.  A packet simple of dimension `D_t` contributes exactly `D_t`
one-dimensional `K` characters, counted with multiplicity.  Let a fresh
packet share `K` as its central selector subgroup, and suppose every selected
fresh simple has dimension `D_s`.  Its restriction to `K` contributes
`D_s` copies of its selector character.

If an ordinary amalgam or HNN edge identifies the two `K` representations,
then, after summing over characters,

```text
D_t times (old simple multiplicity)
  =D_s times (fresh simple multiplicity),                       (QSC1)
```

with the analogous sum when several types occur.  Hence the unweighted
multiplicity can appear to grow by `D_t/D_s`, but the common-scale weighted
multiplicity is unchanged:

```text
D_t m_t/d = D_s m_s/d.                                         (QSC2)
```

In particular, padding the first Schur packet to make `D_t` enormous, or
feeding its character vector into a two-dimensional constant-true rank gate,
does not amplify normalized marked mass.  It merely spends the old spin
dimension as new scalar multiplicity.  Iterating through successively smaller
packets telescopes to the initial/final dimension ratio and cannot beat the
same scale already present in the marked lower bound.

Therefore the flip-free endpoint solves selector forgetting and branch
separation, but an ordinary q-MASA-to-selector incidence cannot solve
`q-masa-to-fresh-packet-morita-bridge`.  The bridge must return at the same
fixed irreducible scale through a proper corner, projective holonomy, or
another genuinely non-Bass--Serre operation.

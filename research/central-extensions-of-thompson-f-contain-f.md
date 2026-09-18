---
rg: 2
id: central-extensions-of-thompson-f-contain-f
kind: claim
title: Thompson's group F has a self-embedding killing all of H^2(F;A), so every central extension of a group containing F contains F
distinct_from:
  thompson-f-bounded-cohomology-vanishes-separable-duals: that is about bounded cohomology of F; this is about ordinary second cohomology with trivial coefficients and its restriction to one explicit copy of F.
  thompson-f-has-infinite-cohomological-dimension: that records cd F = ∞; this shows that extending by an abelian group cannot remove F, so central extensions of Thompson groups never yield F-free groups of infinite cd.
---

**ESTABLISHED** through `central-extensions-of-thompson-f-contain-f-proof` (lane bh-free-24,
2026-09-18; an elementary computation in Brown's homology ring of F, not reviewed). No
novelty is claimed.

**Statement.** View `F` as the dyadic PL homeomorphisms of `[0,1]`. Let `R(t) = 1 − t`, and
let `f * g` be Brown's juxtaposition product: a rescaled `f` on `[0,1/2]` next to a rescaled
`g` on `[1/2,1]`. Then
```text
δ : F → F,   δ(f) = f * (R f R)
```
is an injective homomorphism with `δ^* = 0 : H^2(F;A) → H^2(F;A)` for every abelian group
`A` with trivial action. Consequently:
- **(a)** every central extension `1 → A → E → F → 1` restricts to a split extension over
  `δ(F)`, so `E` contains a copy of `F`;
- **(b)** if a group `Q` contains `F`, every central extension of `Q` by an abelian group
  contains `F`. Examples are `T`, `V` and every Thompson-like group.

**Why it matters.**
- **Witzel's question** (as quoted by FFKLZ, arXiv:2506.02319v2, TeX l.293) asks for a
  torsion-free group of type `F_∞` with infinite cohomological dimension that contains no
  `F`. A central extension of `F` by `Z` is torsion-free, of type `F_∞` and of infinite cd,
  so (b) shows that this natural candidate always contains `F`.
- **FFKLZ Question 2.4** (`oligomorphic-fp-infinity-actor-without-thompson-f`) can have a
  non-faithful witness. This statement kills witnesses obtained as central extensions of
  Thompson-like groups acting through the quotient. The general kernel case is
  `extensions-with-f-free-outer-kernel-contain-thompson-f`.

**The mechanism.** The flip `f ↦ RfR` reverses Brown's product and acts by `−1` on
`H_2(F)`. In `δ`, the two halves cancel.

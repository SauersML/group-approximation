---
rg: 2
id: ascending-hnn-coset-ray-is-folner
kind: claim
title: Intervals of the height ray are explicit Folner sets for the ascending-HNN coset action
distinct_from:
  no-invariant-mean-on-coset-space: that says a *Kazhdan* group has no invariant mean on an infinite-index coset space; this exhibits an invariant mean, by explicit Folner sets, for an ascending HNN extension, which is never Kazhdan because it surjects onto Z.  The two are consistent and are about different groups.
artifacts:
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
  - GroupApproximation/Sofic/AscendingHNNFolner.lean
---

Let `alpha : Gamma -> Gamma` be an injective endomorphism, `V` the ascending
HNN model `N ⋊ <t>` with `N` the directed union of the `t^{-n} Gamma t^n`, and
`X = V/Gamma` its coset space.  Then the base is co-amenable: for every finite
`F` in `V` and every `eps > 0` there are `R` in `Z` and `L > 0` such that the
image of the interval `[R, R+L)` under the ray

    x_j = t^{-j} Gamma

satisfies `|g.A ∆ A| < eps.|A|` for every `g` in `F`.  In particular the ray is
injective, so the intervals really do have `L` elements.

## Why the concrete form is worth having

Co-amenability of the base here is Monod--Popa's theorem, and that it applies to
this ascending-HNN instance — through the directed union `N` with `V = N ⋊ <t>`
— was pointed out by Fournier-Facio.  What this claim adds is the explicit
Følner structure rather than the existence of an invariant mean, in the form the
telescope arguments consume: a *single* ray, one interval per accuracy, and a
bound that is uniform over a prescribed finite set.

The mechanism is worth stating because it explains why the estimate is so cheap.
Deep telescope elements fix the tail of the ray — `t^n x t^{-n}` for `x` in
`Gamma` lands in a level that stabilizes every `x_j` with `j` past some `M(g)` —
so every group element eventually acts on the ray *as the height translation
alone*.  Translation moves an interval by a bounded amount, so the symmetric
difference stays bounded while the interval grows, and two integer intervals of
equal length differ by at most twice their offset.

The ray is indexed by `Z` rather than `N`.  That costs nothing and removes the
case analysis at the near end, which is the only place a `N`-indexed ray would
need care.

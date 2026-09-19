---
rg: 2
id: brick-groupoid-not-isomorphic-to-rs-boundary-host
kind: claim
title: "For every n >= 1 the brick groupoid G_2^n is not isomorphic to the Robertson–Steger host (Gamma x| Omega) x G_2"
distinct_from:
  brick-groupoid-not-isomorphic-to-kazhdan-host: that is the conjunction of the W1 and RS non-isomorphisms; this is the RS half alone, which is what remains after brick-groupoid-has-no-principal-cantor-factor settles W1
  brick-groupoid-has-no-principal-cantor-factor: that proves the isotropy-stratum obstruction and reduces this claim to the stabilizer conditions below; this is the remaining RS question itself
  robertson-steger-tile-groupoids-have-no-spatial-realization: that concerns the 2-graph groupoid of a triangle presentation and spatial realizations; this is an isomorphism question for the boundary action groupoid times G_2
---

**Status: OPEN.**

## Statement

Let `Γ ≤ PGL_3(K)` and `Ω` be as in `rs-boundary-groupoid-is-expansive-amenable-kazhdan-host`,
and let `𝒢_RS = (Γ ⋉ Ω) × G_2`. Then `𝒢_RS ≇ G_2^n` for every `n ≥ 1`.

## Known

By `brick-groupoid-has-no-principal-cantor-factor` (c).4, an isomorphism `𝒢_RS ≅ G_2^n`
forces all of the following:

- (S1) every stabilizer `Γ_ω` is free abelian;
- (S2) the maximal stabilizer rank is `n − 1 ≥ 1`, so `Γ ↷ Ω` is not free and `n ≥ 2`;
- (S3) `{ω : rk Γ_ω = n − 1}` is countable and nonempty.

Two more facts cut this down:

- **Remark in the proof route (standard, uncited).** `cd` bounds for torsion-free subgroups
  acting freely on the 2-dimensional building give `rk Γ_ω ≤ 2`. So only `n ∈ {2, 3}` would
  survive.
- **From the lower strata.** At rank `n − 1` in `G_2^n`, the stratum `p^{-1}(n−1)` is
  uncountable. It must be matched by
  `{ω : rk Γ_ω = n − 1} × (C \ E) ∪ {ω : rk Γ_ω = n − 2} × E`.
  This is automatic once (S3) holds, so no contradiction comes from counting alone.

## Attempts

- **2026-09-19 (swarm-0917-w16-w16-nv-break, finite-models): counting isotropy strata
  (partial; dies at the non-free case).**
  - The top-stratum count of `brick-groupoid-has-no-principal-cantor-factor` settles the free
    case and `n = 1`.
  - It dies where the boundary action has a countable, nonempty set of points with stabilizer
    rank `n − 1 ≥ 1`. Cardinalities of strata then match (see Known), so counting alone cannot
    decide the claim.
- **Deferred: fixed-set germs.** `regular-rank-two-isotropy-blocks-spatial-realization-in-g2n` records
  that in `G_2^n` every lag with a zero coordinate fixes a coordinate slice.
  - For topological isomorphisms, the **non-regular locus**
    `N(x) = {g ∈ G_x^x : x not isolated in Fix(g)}` is an invariant.
  - In `G_2^n` at a top point `x ∈ E^n`, `N(x)` is the union of the `n` coordinate
    hyperplanes of `Z^n`. Each is a rank-`(n−1)` subgroup.
  - Now take `𝒢_RS` at `(ω, e)`, where `A = Γ_ω ≅ Z^2` lies in a split torus and no
    nontrivial element has a repeated eigenvalue (the hypothesis of item 1 of that node's
    worked applications). The fixed set of `(a, k)` is `Fix(a) × Fix(k)`, so
    `N = (A × {0}) ∪ ({1} × Z)`. This is one rank-2 subgroup and one rank-1 subgroup.
  - It is not a union of three rank-2 subgroups, which excludes `n = 3`. Such an `A` has rank
    3 in total, which excludes `n = 2`. The cd remark excludes `n ≥ 4`.
  - So the RS half follows **conditionally** on such an `A` existing. The existence input
    (S-unit theorem, or periodic flats with distinct eigenvalues) is exactly the uncited one
    in `regular-rank-two-isotropy-blocks-spatial-realization-in-g2n`.
  - This paragraph is a sketch, not a proof, and is not claimed.
- **Either way, the case needs** the existence (or absence) of `Z^2 ≤ Γ` in a split torus,
  which is not established on the graph.

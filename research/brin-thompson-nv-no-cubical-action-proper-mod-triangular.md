---
rg: 2
id: brin-thompson-nv-no-cubical-action-proper-mod-triangular
kind: claim
title: "For n >= 2 no commensurating action of nV (no action on a CAT(0) cube complex or wall space) is proper modulo the triangular subgroup T_n, or modulo any undistorted subgroup"
distinct_from:
  brin-thompson-mv-contains-a-distortion-element: that records Callard--Salo's corollary that mV has no proper cubical action (properness modulo the trivial subgroup); this rules out properness modulo the large subgroup T_n, which contains C(C,V) ⋊ V and V^n, so cubical geometry cannot even supply the transversal half of a split along T_n
  brin-thompson-nv-stein-farley-complex-is-not-cat0: that shows one specific complex is not CAT(0); this excludes every commensurating action, for a relative notion of properness
  brin-thompson-brick-charts-are-not-commensurated: that kills one candidate commensurated set; this kills all of them modulo T_n
---

**ESTABLISHED** by `brin-thompson-nv-no-cubical-action-proper-mod-triangular-proof`.

**Statement.** Let `n ≥ 2`, and let `H ≤ nV` be a subgroup whose infinite-order elements are
undistorted in every finitely generated subgroup of `nV` containing them. Examples:
`T_n`, its conjugates, its images under coordinate permutations, and all their subgroups
(`brin-thompson-triangular-subgroup-is-undistorted`).

1. No commensurating action of `nV` has wall count `ℓ(g) = |gA Δ A|` proper modulo `H`. In
   particular no action of `nV` on a CAT(0) cube complex, or on a discrete wall space, has
   displacement `d(v, gv)` proper modulo `H`.
2. More precisely, let `f` be the Callard–Salo element. Then the powers `f^N` lie in pairwise
   distinct cosets of `H`, and every commensurating action has `ℓ(f^N)` bounded. So a cnd function
   `ψ_1` proper modulo `H` must satisfy `ψ_1(f^N) → ∞` and `ψ_1(f^N) = O(log^8 N)`, and cannot be a
   finite sum of wall counts.

**What this kills.** The route "Farley-type walls give the transversal (coset) direction, and
a fibrewise Haagerup statement (Brothier's Problem B, iterated) gives properness on `T_n`" through
`haagerup-splits-as-coset-plus-subgroup-properness`. Its transversal half must be a genuinely
non-cubical cnd function: an infinite weighted sum of wall counts, or a function from a
non-commensurating representation, with polylogarithmic but unbounded growth on the distorted
cyclic subgroup `⟨f⟩`.

**Invariant and death step.** The invariant is the growth of the function along the distorted
cyclic subgroup `⟨f⟩`. Every cubical candidate dies at the bounded-or-linear dichotomy (sublinear
growth forces boundedness), followed by the pigeonhole into finitely many cosets, which would put
a power of `f` into `H`, where it would be undistorted.

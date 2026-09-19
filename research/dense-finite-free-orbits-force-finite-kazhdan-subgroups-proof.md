---
rg: 2
id: dense-finite-free-orbits-force-finite-kazhdan-subgroups-proof
kind: route
title: "Free finite orbits embed in A × F_d, so they are uniformly bounded; the bounded-orbit set is closed, hence everything; finitely many bounded-index subgroups then kill K"
target: dense-finite-free-orbits-force-finite-kazhdan-subgroups
requires:
  - kazhdan-orbit-bound-in-amenable-by-free-groups
---

Notation as in the target. By Step 0 of
`kazhdan-orbit-bound-in-amenable-by-free-groups-proof`, `K` has a Kazhdan pair `(S, ε)`
with `S` finite, symmetric and generating. Let `E = ∪_{s ∈ S} c_s(X)`. This is a finite
subset of `P`, since each `c_s` is continuous from a compact space to a discrete one. Let
`M` be the bound of `kazhdan-orbit-bound-in-amenable-by-free-groups` for `(S, ε, E, A, d)`.

## Step 1. Free finite orbits are bounded by M

Let `x ∈ X_free` with `Z = Kx` finite. Each `g ∈ K` moves every point inside its
`P`-orbit, so `Z ⊂ Px`. As `x` is free, each `y ∈ Z` is `p·x` for a unique `p =: ι(y)`, and
`ι` is injective. For `s ∈ S`, `sy = c_s(y)·y = (c_s(y) ι(y))·x`, so
`ι(sy) = c_s(y) ι(y) ∈ E·ι(y)`. `Z` is a finite transitive `K`-set, so the lemma gives
`|Z| ≤ M`.

## Step 2. All orbits are bounded by M

Let `Y = {x ∈ X : |B_S(M)·x| ≤ M}`, where `B_S(M)` is the finite set of words of length
`≤ M` in `S`.

- *`Y` is the set of points with `|Kx| ≤ M`.* If `|Kx| ≤ M`, the Schreier graph on `Kx` is
  connected with at most `M` vertices. So `Kx = B_S(M−1)x` and `x ∈ Y`. Conversely, if
  `x ∈ Y`, the sets `B_S(r)x`, `r = 0, …, M`, increase and have sizes between `1` and `M`.
  So `B_S(r)x = B_S(r+1)x` for some `r < M`. Then `S·B_S(r)x ⊂ B_S(r)x`, and as `S`
  generates `K` and the set is finite, it is `K`-invariant. So `Kx = B_S(r)x` has at most
  `M` points.
- *`Y` is closed.* List `B_S(M) = {g_1, …, g_N}`. Then `X \ Y` is the union, over the
  index sets `I` of size `M+1`, of `{x : the points g_i x, i ∈ I, are pairwise distinct}`.
  Each of these is open because `X` is Hausdorff and the `g_i` are continuous.
- *`Y` contains a dense set.* By Step 1 it contains `{x ∈ X_free : Kx finite}`, which is
  dense by hypothesis.

So `Y = X`.

## Step 3. K is finite

A finitely generated group has finitely many subgroups of index `≤ M`. A subgroup `H` of
index `m` is the stabiliser of `1` in a transitive action on `{1, …, m}`, obtained by
numbering `K/H` with `H ↦ 1`. That action is determined by the images of the `|S|`
generators in `Sym(m)`. So there are at most `Σ_{m ≤ M} (m!)^{|S|}` such subgroups.

Let `N` be their intersection, a subgroup of finite index. For every `x`,
`[K : Stab_K(x)] = |Kx| ≤ M` by Step 2, so `N ≤ Stab_K(x)`. Thus `N` fixes every point
of `X`. Elements of `K` are homeomorphisms of `X`, so `N = 1`, and
`|K| = [K : N] < ∞`. ∎

## The Corollary

- (1) ⇒ (2): trivial.
- (2) ⇒ (3), and then (1): if `X_free` is dense, (2) makes the hypothesis of the theorem
  hold, and Step 1 gives the bound `M`.
- (3) ⇒ (1): the orbits through the dense set `X_free` are then finite, and the theorem
  applies.

The density of `X_free` for `Ω × ∂F_d` is shown in the target. For a hyperbolic
`w ≠ 1` in `F_d`, the fixed points on `∂F_d` are `w^{±∞}`, and there are countably many
`w`. The space `∂F_d` is a Cantor set for `d ≥ 2`, so the complement of a countable set is
dense in it (Baire). The two bullet points after the Corollary in the target are proved
there in full.

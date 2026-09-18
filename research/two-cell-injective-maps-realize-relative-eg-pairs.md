---
rg: 2
id: two-cell-injective-maps-realize-relative-eg-pairs
kind: claim
title: A subgroup pair is relatively realizable iff some combinatorial map from a 2-dimensional K(H,1) to a 2-dimensional K(G,1) is injective on 2-cells (1-cells may fold), iff G acts on a contractible 2-complex freely off one vertex orbit with stabilizer H; admissible bases in one-relator groups have H_2 zero or mapping isomorphically, and w-disc subgroups realize
distinct_from:
  relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two: that defines RP by a subcomplex and characterizes it by an uncountable amalgam; this weakens the subcomplex to a map that may identify 1-cells and vertices and only has to be injective on 2-cells, and gives the equivariant cone-off form.
  trees-of-groups-with-realizable-edges-realize-vertices: that realizes vertex groups of splittings; this realizes subgroups carried by 2-cell-injective maps, which need not be vertex groups of any splitting.
  relative-eg-pair-base-meets-its-conjugates-in-free-groups: that proves H_2(H) injects into H_2(G); this adds that the cokernel is free abelian, which in one-relator groups forces degree one.
artifacts: []
---

**ESTABLISHED** through `two-cell-injective-maps-realize-relative-eg-pairs-proof`. Unreviewed. No novelty is claimed for the collapse in part 1, which is an elementary mapping-cylinder argument; the point is what it frees up for the relative Eilenberg--Ganea search.

## Conventions

- `RP(H,G)` is as in `relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two`: some 2-dimensional `K(G,1)` has an aspherical subcomplex inducing `H ≤ G`. No countability is needed below.
- A cellular map `f: K → X` of 2-complexes is **combinatorial** if it maps each open cell homeomorphically onto an open cell of the same dimension, compatibly with characteristic maps (`f ∘ Φ_e = Φ_{f(e)} ∘ h_e` for a homeomorphism `h_e` of the disc).
- It is **2-cell-injective** if distinct 2-cells of `K` go to distinct 2-cells of `X`. Nothing is required of vertices and edges: `f` may fold the 1-skeleton.

## Statement

**1. Realization criterion.** For groups `H ≤ G` the following are equivalent.

- **(a)** `RP(H,G)`.
- **(b)** There are a 2-dimensional `K(G,1)` `X`, a 2-dimensional `K(H,1)` `K` and a 2-cell-injective combinatorial map `f: K → X` inducing `H ≤ G` on `π_1`.
- **(c)** Some 2-dimensional `K(G,1)` `X` has, in its cover `X_H` for `H`, a subcomplex `K` with `π_1 K → π_1 X_H` an isomorphism that contains at most one lift of each 2-cell of `X`.
- **(d)** `G` acts freely and cellularly on a contractible 2-complex `X̃` that contains an `H`-invariant contractible subcomplex `C` such that `C` and `gC` share no 2-cell for every `g ∈ G ∖ H`.
- **(e)** `H` has a 2-dimensional `K(H,1)`, and `G` acts cellularly on a contractible 2-dimensional complex `Y` with one orbit of vertices of stabilizer `H` and all other cells freely permuted.

In (d) the translates may share edges and vertices. So the intersections `C ∩ gC` are graphs, which matches the free intersections `H ∩ gHg^{-1}` forced by the pd hypothesis.

**2. Purity (from the pd hypothesis alone).** If `pd_{ZG} I_{G/H} ≤ 1`, then `H_2(H) → H_2(G)` is injective and its cokernel is free abelian.

**3. One-relator groups.** Let `G = ⟨S | w⟩` with `w` cyclically reduced and not a proper power.

- **(3a) Admissible bases have degree 0 or 1.** If `pd I_{G/H} ≤ 1`, then either `H_2(H) = 0`, or `w ∈ [F(S),F(S)]` and `H_2(H) → H_2(G) ≅ Z` is an isomorphism. In particular:
  - a closed orientable surface subgroup of genus `≥ 1` is admissible only if `w ∈ [F,F]` and the surface has degree `±1` onto the relator class;
  - if `w ∉ [F,F]`, no admissible base has nonzero `H_2`.
- **(3b) w-disc subgroups realize.** Let `Γ` be a connected graph with a combinatorial map to the rose `R_S` (labels in `S^{±1}`; *not* required to be an immersion), and `u` a closed edge path in `Γ` whose label is `w`. If `π_1(Γ)/⟨⟨u⟩⟩ → G` is injective with image `H`, then `RP(H,G)`.

## What this does for the minimal counterexample

The base `H` of a pair whose `ℵ_1`-fold amalgam refutes Eilenberg--Ganea must satisfy, for **every** 2-dimensional `K(G,1)` `X` (of `G` and, by descent, of every realizable overgroup):

- **every** `π_1`-isomorphic subcomplex of the cover `X_H` contains two lifts of some 2-cell of `X`.

This is a finite, checkable condition on a finite core when `X` is finite and `H` is finitely generated. It turns the relative search into a search for 2-cell-injective cores, a compute-scout target.

In one-relator groups the surviving candidates are narrow:

- `H_2(H) = 0` bases, or degree-one bases when `w ∈ [F,F]`;
- that are not carried by any w-disc.

The Klein bottle calibration is consistent: every core of the torus cover of the one-square Klein bottle uses both lifts of the square.

---
rg: 2
id: fp-dense-cantor-subgroups-need-not-have-fg-clopen-stabilizers
kind: claim
title: A generic free product V * Z inside Homeo(Cantor) is a finitely presented dense subgroup none of whose clopen stabilizers is finitely generated
requires:
  - permutational-boone-higman-iff-dense-cantor-actors
refuted_by:
  - v-and-a-homeomorphism-never-generate-a-free-product
distinct_from:
  permutational-boone-higman-iff-dense-cantor-actors: that proves PBH is equivalent to embedding in a finitely presented dense subgroup of Homeo(C) with finitely generated clopen stabilizers; this shows the stabilizer clause cannot be dropped, since finite presentation plus density does not give type (A) on clopens.
  fp-full-binary-cantor-groups-have-type-a-actions: that gives finitely generated clopen stabilizers for finitely presented FULL groups containing standard V; the group here contains standard V and is not full.
---

**REFUTED** (09-18, bh-free-19) by `v-and-a-homeomorphism-never-generate-a-free-product`:
for every `t ≠ 1` the relation `[[t,a],b] = [a^{-1},b]` (with `a, b ∈ V` supported in a
clopen `U` that `t` moves off itself) holds in `Homeo(C)` but not in `V * ⟨t⟩`, so
`⟨V,t⟩` is never the free product. The Baire argument below fails at "freshness makes
every point produced by a `v_i` new": syllables of `V` fix open sets pointwise, so a
fresh point can be fixed and the reading collapses. The text below is kept as the
record of the refuted claim. (It was: lane proof, elementary, not reviewed.)

Let `C = {0,1}^N`, give `Homeo(C)` the compact-open topology, and let `V ≤ Homeo(C)`
be standard Thompson's `V`. Let `Ω` be the set of proper nonempty clopen subsets.

**Theorem.**
1. For a comeager set of `t ∈ Homeo(C)`, the subgroup `⟨V, t⟩` is the free
   product `V * ⟨t⟩ ≅ V * Z`.
2. For every such `t` and every `U ∈ Ω`, the stabilizer `Stab_{⟨V,t⟩}(U)` is not
   finitely generated. It maps onto a free group of infinite rank.

So `Γ = ⟨V,t⟩` is finitely presented (a free product of finitely presented groups)
and dense (it contains `V`, which is dense). Yet its action on `Ω` is not of type
(A). Finite presentation plus density does not force the stabilizer clause of
`permutational-boone-higman-iff-dense-cantor-actors`. This is not a counterexample
to PBH: `V * Z` lies in `B_A` by closure under free products (BFFHZ Corollary F, as
recorded in `permutational-boone-higman-conjecture`). Only its clopen action fails
to be of type (A).

## Proof of 1

`V` is countable, so there are countably many nontrivial `w ∈ V * ⟨x⟩`. For each,
`Z_w = {t : w(t) ≠ 1}` is open, since evaluation is continuous. By Baire it suffices
to show each `Z_w` is dense. If `w ∈ V` there is nothing to prove, so write `w` in
reduced form `v_0 x^{n_1} v_1 ⋯ x^{n_k} v_k`, with `k ≥ 1`, all `n_i ≠ 0`, and
`v_1, …, v_{k-1} ≠ 1`.

A nonempty basic open set has the form `O = {s : s(A_j) = B_j, j ≤ m}` for two clopen
partitions `{A_j}`, `{B_j}` of the same size. Build a finite injective partial map
`τ`, sending points of `A_j` into `B_j`, by reading `w` from right to left starting
at a point `p`.
- Apply the `v_i` as given.
- Each time `t^{±1}` must be applied to a point where `τ^{±1}` is still undefined,
  choose a **fresh** image (or preimage) in the required atom.
- A fresh choice avoids the finitely many points already in the domain or range of
  `τ`, and their images under the finitely many `v_i^{±1}`. This is possible
  because every atom is a Cantor set.

Freshness makes every point produced by a `v_i` new, so `τ` stays an injective
partial map and every step of the reading is defined. At the last step, choose the
final fresh point `r` with `v_0(r) ≠ p`. A finite injective partial map between
Cantor sets extends to a homeomorphism, atom by atom, so `τ` extends to some
`t ∈ O`. Then `w(t)(p) = v_0(r) ≠ p`. Hence `Z_w ∩ O ≠ ∅`.

## Proof of 2

Let `Γ = V * ⟨t⟩`, `H = Stab_Γ(U)`, and let `T` be the Bass–Serre tree of the free
product. Its vertices are `Γ/V ⊔ Γ/⟨t⟩`, its edges are `Γ`, and edge stabilizers are
trivial. Consider the quotient graph `Y = H\T`.
- **Edges.** `V` is transitive on `Ω`: single clopens have one Boolean pattern. So
  `Γ` is transitive on `Ω`, and `Hγ ↦ γ^{-1}U` is a bijection `H\Γ → Ω`.
- **Vertices of `V`-type.** They are `H\Γ/V`, which corresponds to the `V`-orbits
  on `Ω`. There is exactly one.
- **Vertices of `t`-type.** They are `H\Γ/⟨t⟩`, which corresponds to the
  `⟨t⟩`-orbits `O` on `Ω`. The edge `U' ∈ O` joins the unique `V`-vertex to the
  vertex of `O`.

So `Y` is a star with `|O|` parallel edges to the vertex of each `O`, and `π_1(Y)` is
free of rank `Σ_O (|O| − 1)`. By Bass–Serre theory, `H` maps onto `π_1(Y)` (kill the
vertex groups).

This rank is infinite. Since `t ≠ 1`, it moves some point `x`, and every
sufficiently small clopen `U' ∋ x` satisfies `t(U') ∩ U' = ∅`. So infinitely many
clopens lie in `⟨t⟩`-orbits of size at least 2, which forces `Σ_O (|O|−1) = ∞`. A
finitely generated group has no free quotient of infinite rank, so `H` is not
finitely generated. ∎

## Consequence for the swarm

In the dense-Cantor normal form of PBH, the only content lies in finite presentation
together with finitely generated clopen stabilizers. Free-product enlargements of
`V` are finitely presented and dense but lose the stabilizer clause. So a
construction aiming at PBH through dense Cantor actors must control stabilizers, as
full groups (`fp-full-binary-cantor-groups-have-type-a-actions`) and twisted
Brin–Thompson groups do. Density alone buys nothing.

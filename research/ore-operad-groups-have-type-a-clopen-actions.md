---
rg: 2
id: ore-operad-groups-have-type-a-clopen-actions
kind: claim
title: A finite-type dissection-operad group with Ore's condition acts with type (A) on its accessible clopen sets, without being a full group
distinct_from:
  fp-clopen-transitive-full-cantor-groups-have-type-a-actions: that needs the host to be a full group; this replaces fullness by the operad structure, so it applies to operad groups such as the edge-split group, which contain the derived full group but need not equal the full group.
  non-lcm-dissection-operad-groups-are-f-infinity: that gives finite presentation; this adds the other three conditions of Zaremsky's type (A) for the same groups.
---

**ESTABLISHED** (lane bh-free-54, 2026-09-18). Lane proof below, not independently
reviewed. It uses Thumann's theorem as recorded in
`non-lcm-dissection-operad-groups-are-f-infinity`.

## Statement

- Let `𝒪` be a dissection operad satisfying the hypotheses of
  `non-lcm-dissection-operad-groups-are-f-infinity`: square filling, a finite spine,
  and finite groups of transformations.
- Let `G = G_𝒪` be its group of fractions on `X`. Let `𝒮` be the set of proper
  nonempty clopens that are unions of pieces of some `𝒪`-dissection family of `X`.
- Assume every tile admits a nontrivial subdivision. This holds whenever each color
  is the output of some subdivision, since every input color is then subdivided
  through its own output.
- Then the action of `G` on `𝒮` is of type (A), with all four conditions of
  `type-a-action-gives-boone-higman-for-subgroups`.
  - **Faithful:** `𝒮` separates points.
  - **Finitely presented:** `G` is `F_∞` by Thumann.
  - **Stabilizers finitely generated:** `Stab_G(U) ≅ π_1(𝒪, U) × π_1(𝒪, X∖U)`, and
    both factors are `F_∞`.
  - **Finitely many orbits:** at most 16 orbits of ordered pairs.
- So every subgroup of `G` embeds in a finitely presented simple group.

## Proof

- **`𝒮` is `G`-invariant.** Refine a dissection so that `U` is a union of its pieces
  and `g` is a fraction on it. The image of `U` is then a union of pieces of the image
  dissection.
- **Stabilizers.**
  - Suppose `g ∈ Stab(U)`. By Ore's condition, choose `𝒪`-dissections `C ↦ gC`
    representing `g`, such that `U` is a union of pieces of both. Both restrictions
    should refine a fixed dissection `C_U` of `U`: take common refinements with the
    dissection `C_U` witnessing `U ∈ 𝒮`, on both sides.
  - Then `g|_U` is a fraction between two refinements of `C_U|_U`. That is an element
    of the operad group at the object `U` (the tuple of colors of `C_U|_U`).
    Similarly for `X ∖ U`.
  - Conversely, any two such fractions glue to an element of `G`.
  - Thumann's theorem holds at every object, so both factors are `F_∞`.
- **Orbits of pairs.**
  - For `(U, U')` in `𝒮`, the four regions `U ∩ U'`, `U ∖ U'`, `U' ∖ U` and the rest
    are unions of pieces of one common refinement (Ore).
  - Two pairs whose nonempty regions match can be given dissections with equal piece
    counts in corresponding regions. Refining a piece adds at least one piece, and
    regions of the same type are equalized by refining further. Take the same tile
    colors wherever colors differ; with one color, this is automatic.
  - The fraction matching those dissections region by region lies in `G` and maps one
    pair to the other.
  - So orbits are determined by which regions are nonempty: at most 16.
  - With several colors, finitely many color patterns can occur for each region type,
    and the count stays finite.
- **Faithful.** Accessible clopens form a basis of `X` under the germ-generating
  hypothesis of `ore-operad-groups-contain-the-derived-full-group`, or whenever
  pieces can be made arbitrarily small. A nontrivial element moves some such set.

## Lesson for general BH

- **Fullness can go.** For operad hosts, fullness is not needed for the type (A)
  payoff. The operad structure gives the product decomposition of stabilizers and the
  transitivity on configurations that fullness gave before.
- **The full Cantor-host route, in operad form.** One finite-type Ore operad whose
  group contains the input (directly, or through
  `ore-operad-groups-contain-the-derived-full-group` for perfect inputs) gives
  Boone–Higman for the input and all its subgroups.

---
rg: 2
id: cross-layer-separable-modifications-kill-quantum-rigidity
kind: claim
title: Over any finitely generated group, a fibre product of SFTs is not quantum rigid as soon as one layer's modification set can be translated arbitrarily far from another's; over Z^d, opposite half-space freedoms in two layers are fatal and non-opposite ones never are
requires:
  - minimal-sfts-with-a-finite-modification-are-not-quantum-rigid
distinct_from:
  quantum-rigidity-is-not-closed-under-fibre-products: that kills one fibre product of two group shifts through the antipodal wall theorem; this kills every fibre product of arbitrary SFTs over any group whose layers have separable modification sets, using only the far-modification lemma, and corrects that node's first design rule.
  minimal-sfts-with-a-finite-modification-are-not-quantum-rigid: that needs two far modifications of ONE point of ONE shift; in a fibre product the layers supply them independently, and translation places them.
---

**ESTABLISHED** (lane bh-free-09, 2026-09-18; elementary lane proof, not independently reviewed; no
priority claimed). The proof is given in full below.

## Setting

- `Λ` is infinite and finitely generated, with a word metric `d`. It acts by `(λ·x)(h) = x(λ^(-1)h)`.
- For points `x, x'` of a subshift, `Δ(x, x') = {h : x(h) ≠ x'(h)}`.
- **Separable sets.** Two sets `P, Q ⊆ Λ` are *separable* if for every `R` there is `λ ∈ Λ` with
  `d(P, λQ) > R`.
- `Y ⊆ A^Λ` and `Z ⊆ B^Λ` are SFTs, and `Y × Z` is their fibre product over `Λ`.

## Theorem

1. **Fibre products.** Suppose there are `y ≠ y'` in `Y` and `z ≠ z'` in `Z` such that `Δ(y, y')` and
   `Δ(z, z')` are separable. Then `Y × Z` is not `D`-quantum rigid for any `D`, over any field.
2. **Half-spaces over `Z^d`.** Over `Λ = Z^d`, suppose `Δ(y, y') ⊆ {⟨n, v⟩ > 0}` and
   `Δ(z, z') ⊆ {⟨n, v⟩ < 0}` for one vector `v`. Then these sets are separable, so `Y × Z` is not
   rigid. Conversely, two half-spaces with non-opposite normals meet after every translation.
   So half-space freedoms of two layers are harmful **exactly when they are antipodal**.
3. **Coupled layers.** The same conclusion holds for any SFT `X` (layered or not) that has a point
   `x` with two modifications whose difference sets are at distance `> 2D`. Fibre products are the
   case in which the layers can be modified and translated independently.

**Proof.**
- *Item 3* is the far-modification Lemma of
  `minimal-sfts-with-a-finite-modification-are-not-quantum-rigid`. That lemma needs no finiteness,
  minimality or amenability.
- *Item 1.* Fix `D`, and choose `λ` with `d(Δ(y, y'), λΔ(z, z')) > 2D`. Put `x = (y, λ·z)`,
  `x_1 = (y', λ·z)` and `x_2 = (y, λ·z')`.
  - All three are points of `Y × Z`, because a fibre product contains every pair.
  - `Δ(x, x_1) = Δ(y, y')` and `Δ(x, x_2) = λΔ(z, z')`.
  - Item 3 applies.
- *Item 2.* Take `u ∈ Z^d` with `⟨u, v⟩ > 0`. Then `−Nu + {⟨n, v⟩ < 0} ⊆ {⟨n, v⟩ < −N⟨u, v⟩}`,
  whose distance from `{⟨n, v⟩ > 0}` tends to infinity with `N`. If the normals are not opposite,
  the half-spaces contain a common ray after any translation. `∎`

**Recovered.** Item 1 of `quantum-rigidity-is-not-closed-under-fibre-products` follows from item 2
with `v = e_1`: Ledrappier's shift differs from `0` only west, and its mirror image only east. The
antipodal wall theorem and the group structure are not needed.

## Corrected design rule

**All modifications of every point of a rigid SFT must be pairwise inseparable.** In a layered
design the dangerous pairs are cross-layer.
- *Over `Z^d` grids, with half-space freedoms:* no two layers may have antipodal freedoms.
- *What was wrong.* The earlier rule "give every layer a common open determinism cone" is false as
  stated. Ledrappier's shift and its mirror image share the open rule cone of directions
  `(−10°, 100°)`, and their product is not rigid.
- *Why cones worked in bh-invent-04's transplants.* There the base point is readable from the
  fibre's cone at every site. That is (F2) of `a2-busemann-transplant-rigidity-proof`, and it leaves
  the base no freedom that the cone cannot see (see `cylinder-transport-closure-certifies-centrality`).

## Audit (design analysis; only the parts marked *checked* rest on proofs)

- **Relative seeds (bh-invent-03, 5deee01840): no clash.**
  - Modifications of a glued point are of three kinds: moving the sink, which changes pointers along
    a tree path through the old sink coset; changing a seedless sink configuration inside a rigid
    `Y_ε`; and moving an end, which changes a tail of the ray to the old end.
  - Any two modifications of one point share the old sink coset or a tail of that ray, so they are
    not separable. This is consistent with the gluing proof, which gets cross-type centrality from
    **exclusivity atoms**: each tree edge has, on one side, an isolated-point seed cylinder.
  - That is a third source of (C), next to fibre determinism and product groups. An interface
    carried by a single classical point has no freedom on one side, so no antipodal pair can form
    across it.
- **Square simulations over `Λ₁ × Λ₁` (`minimal-free-sft-via-minimal-self-simulation-of-squares`).**
  - *Input layer (checked):* `Y_1 ⊠ Y_1` is safe. Modifications of the two copies are slabs
    `S × Λ₁` and `Λ₁ × S'`, which always cross. This is why product-group layering never clashes.
  - *Computation layer:* its ambiguity is forced
    (`bounded-determination-simulations-only-realize-sft-shadows`). By item 3 that ambiguity cannot
    sit in bounded zones, so it lives in infinite zones.
  - **Clash risk.** Robinson-type hierarchies have points with two or four infinite zones separated
    by fault lines. An irreversible machine is ambiguous toward the past of each zone. Two zones on
    opposite sides of a fault then carry antipodal, separable ambiguities, and item 3 kills rigidity.
  - **Fix.**
    - (i) Use a skeleton whose points have at most one infinite zone, or nested infinite zones with a
      common tail, so that all infinite-zone ambiguities of a point overlap coarsely.
    - (ii) Orient the time arrows of all grids along the skeleton's own one-sided freedom, so that
      every half-space freedom points the same way. Same-direction half-spaces are never separable.
    - (iii) Before any G2 attempt, list the modification sets per layer and check pairwise
      inseparability. This is a cheap test that needs no quantum family.

## Lesson for general BH

- **Rigidity forbids independent freedoms that can be pulled apart,** within a layer and across
  layers.
- **Fibre products create exactly such pairs.** They let different layers be modified and
  translated independently. Product groups do not, since slabs always cross.
- **The classifying invariant for G2 designs** is the coarse position of each layer's modification
  sets: they must be pairwise inseparable. Over `Z^d`, that means no antipodal half-space freedoms
  anywhere.

---
rg: 2
id: quantum-rigidity-is-not-closed-under-fibre-products
kind: claim
title: Ledrappier's shift and its mirror image are quantum rigid, but their fibre product over the same Z^2 is not; centrality (C) fails there, and a transport closure certifies (C) exactly when no layer's one-sided freedom escapes the other's rules
requires:
  - permutive-triangle-sfts-are-quantum-rigid
  - antipodal-one-sided-group-shift-configurations-are-walls
  - extension-rigidity-is-base-centrality-plus-pointwise-rigidity
distinct_from:
  quantum-rigidity-is-product-stable: that proves rigidity of X ⊠ Y over the PRODUCT group Λ₁ × Λ₂; this shows that the fibre product over ONE group can fail, so coupling two rigid layers on the same group is the dangerous operation.
  antipodal-one-sided-group-shift-configurations-are-walls: that kills one group shift with an antipodal pair; here each factor has one-sided configurations in one direction only (so each is rigid), and the antipodal pair appears only across the two layers.
  a2-busemann-transplants-preserve-quantum-rigidity: that proves (C) for one coupled design by cylinder transport along an open determinism cone; item 3 here is the site version of that transport for fibre products over any group, and item 1 shows what happens when the cones point apart.
---

**ESTABLISHED** through `fibre-product-rigidity-kill-and-transport-proof` (lane bh-free-09,
2026-09-18; elementary lane proof from the three required nodes, not independently reviewed; no
priority claimed).

## Setting

Quantum families (Q1)–(Q3) and `D`-quantum rigidity are as in
`fp-v-times-subshift-full-groups-force-quantum-rigidity`. For SFTs `Y ⊆ A^Λ` and `Z ⊆ B^Λ` over
the same group, the **fibre product** is `Y × Z ⊆ (A × B)^Λ`, the set of pairs `(y, z)` read
sitewise. With `Y` as base and `Z` as fibre it is an extension, in the sense of
`extension-rigidity-is-base-centrality-plus-pointwise-rigidity`, whose fibre over every base point
is `Z` itself.

## Theorem

1. **Kill.** Over `Λ = Z²` and `F_2`, let
   - `Z = {z : z(t) + z(t+e_1) + z(t+e_2) = 0 for all t}`, which is Ledrappier's shift;
   - `Y = {y : y(t) + y(t−e_1) + y(t+e_2) = 0 for all t}`, its mirror image under `(a, b) ↦ (−a, b)`.

   Then:
   - `Y` and `Z` are `D`-quantum rigid over every field, for every `D ≥ 1`;
   - `Y × Z` is not `D`-quantum rigid over any field, for any `D`;
   - `LC(Y × Z, k) ⋊ Z²` is not finitely presented.

   Relative to each base point, the fibre is rigid. So **(C) fails**: some quantum family of `Y × Z`
   has a `Y`-marginal that does not commute with a `Z`-marginal.
2. **Obstruction for group shifts.** Let `Y, Z ⊆ (F_p^m)^(Z²)` be group shifts. Suppose some
   direction `v` has a nonzero `y ∈ Y` supported in `{⟨n, v⟩ > 0}` and a nonzero `z ∈ Z`
   supported in `{⟨n, v⟩ < 0}`. Then `Y × Z` is not quantum rigid.
3. **Transport criterion (any finitely generated `Λ`).**
   - *Rules.* A *rule* of `Z` is a finite `F ⊆ B_D \ {e}` such that, in `Z`, the letter at `t` is a
     function of the letters at `tF`, for every `t`. Rules of `Y` are defined the same way.
   - *The closure `K`.* Let `K ⊆ Λ` be the least set that contains `B_(2D)` and satisfies:
     - (Z-step) if `f^(-1) k ∈ K` for all `f` in a rule of `Z`, then `k ∈ K`;
     - (Y-step) if `k f ∈ K` for all `f` in a rule of `Y`, then `k ∈ K`.
   - *Conclusion.* In every `D`-family of `Y × Z`, the `Y`-marginal at `vk` commutes with the
     `Z`-marginal at `v` whenever `k ∈ K`. So if `K = Λ`, (C) holds. If moreover `Y` and `Z` are
     `D`-rigid, then `Y × Z` is `D`-rigid.
   - *In the example of item 1,* `K ⊆ {a ≤ 2D}` for every `D`. `Z` has no rule in the open east
     half-plane and `Y` has none in the open west half-plane. So the certificate is blocked
     exactly along the antipodal direction `e_1` that item 1 exploits.

## Why it matters

- **Products versus fibre products.** Rigidity is stable under products over product groups
  (`quantum-rigidity-is-product-stable`) and under deterministic extensions
  (`deterministic-extensions-of-rigid-sfts-are-rigid`). It is **not** stable under the most
  innocent coupling of all: two independent rigid layers on one group.
- **What (C) is.** The decomposition theorem says that (C) is the whole G2 content of a layered
  design. Item 1 is the first explicit failure of (C) with both layers rigid. It is also the first
  failure with a fibre that is rigid relative to every base point.

## Lesson for general BH

- **Rigidity is a property of how layers see each other across distance, not of the layers.**
  A layer can have *one-sided freedom* in a direction `v`: a nonzero change supported in a half-space
  `{⟨n, v⟩ < 0}`, which also kills that layer's rules on the far side. Two such layers with opposite
  one-sided freedoms superpose to a wall.
- **Design rule for G2.** Every direction in which one layer has one-sided freedom must be covered by
  a rule of another layer (transport closure `K = Λ`).
  - Operationally: give all layers a **common open determinism cone**.
  - This is what makes bh-invent-04's tree and `Ã₂` transplants work. There the sector cylinders of
    the germ layer transport along the tile layer's open-cone determinism (`M e_i` in the open
    cone).
  - It is also exactly what can go wrong in a simulation over `Λ₁ × Λ₁`, where skeleton, data and
    computation layers live on one group.

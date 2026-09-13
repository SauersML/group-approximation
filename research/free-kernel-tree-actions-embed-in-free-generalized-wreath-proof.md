---
rg: 2
id: free-kernel-tree-actions-embed-in-free-generalized-wreath-proof
kind: route
title: Record the projected geodesic edge word, check the cocycle identity by cancelling backtracks, and read off injectivity from the covering map
target: free-kernel-tree-actions-embed-in-free-generalized-wreath
requires:
  - gkp-free-generalized-wreath-soficity
  - gkp-wreath-permanence-theorem
  - gkp-sofic-action-toolkit
---

# Proof

**Setup.**
* *The covering.* Since `Λ` acts freely without inversions and `T` is simply connected, the map
  `π : T → Y` is a covering with deck group `Λ`, and `π_1(Y, πv_0) ≅ Λ`.
* *The action on `Y`.* `Q` acts on `Y` by `gΛ·πu = π(gu)`. This is well defined because `Λ` is
  normal, and `π(g·β) = gΛ·π(β)` for every edge path `β`.
* *Local injectivity.* `Λ` acts freely on vertices, so `π` is injective on the star of each vertex.
  So distinct edges at `u` map to distinct oriented edges at `πu`.

**Target groups.**
* *Free lamps.* Let `F_Y` be the free group on `E^±(Y)` modulo `ē = e^(−1)`, i.e. the free group on
  one orientation of each edge. `Q` acts on it by automorphisms, since it permutes `E^±(Y)` and
  commutes with reversal. The map `F_Y → *_(E^±(Y)) Z_e`, `e ↦ e·ē^(−1)`, is `Q`-equivariant. It is
  compatible with `ē = e^(−1)` and injective, because the elements `e·ē^(−1)`, one per orientation
  representative, are part of a free basis. So `F_Y ⋊ Q ↪ Z ≀^*_(E^±(Y)) Q`.
* *Abelian lamps.* Likewise `C_1(Y) = Z[E^±(Y)]/(e + ē) ↪ Z[E^±(Y)]` by `e ↦ e − ē`, and
  `C_1(Y) ⋊ Q ↪ Z ≀_(E^±(Y)) Q`.

**Cocycle.** Fix `v_0 ∈ T`. For `g ∈ Γ` let `γ_g` be the geodesic edge path from `v_0` to `gv_0`, and
let `d(g) ∈ F_Y` be the word of oriented edges of `π(γ_g)`.
* *Paths reduce to geodesics.* Every edge path `β` in `T` from `u` to `w` reduces to the geodesic
  by cancelling backtracks `e·ē`. Their images `πe·(πe)^(−1)` cancel in `F_Y`, so `π_*(β) = π_*(γ)` in
  `F_Y`, where `γ` is the geodesic.
* *The identity.* `γ_g · g(γ_h)` runs from `v_0` to `ghv_0`, so

  ```text
  d(gh) = d(g) · π_*(g γ_h) = d(g) · (gΛ)·d(h).
  ```

  Hence `Φ(g) = (d(g), gΛ)` is a homomorphism `Γ → F_Y ⋊ Q`.

**Item 1.** Suppose `Φ(g) = 1`. Then `g ∈ Λ`. The geodesic `γ_g` has no backtracking. By local
injectivity `π(γ_g)` has none either, so its edge word is reduced in `F_Y`. It is therefore trivial
only if `γ_g` is empty, i.e. `gv_0 = v_0`. Then `g ∈ Λ ∩ Stab(v_0) = 1`. Compose with the embedding of
the target groups.

**Item 2.** Let `d^ab(g)` be the image of `d(g)` in `C_1(Y)`. Then `Φ^ab = (d^ab, ·Λ)` is a
homomorphism `Γ → C_1(Y) ⋊ Q`, and its kernel lies in `Λ`. For `g ∈ Λ`, `π(γ_g)` is a closed loop at
`πv_0` representing `g ∈ π_1(Y)`, and `d^ab(g)` is its class in `Z_1(Y) = H_1(Y)` (a graph has no
2-cells). By covering theory `H_1(Y) = Λ^ab`, so the kernel is `[Λ,Λ]` and `Φ^ab` induces an embedding
of `Γ/[Λ,Λ]`.

**Item 3.**
* *The set action.* By `gkp-sofic-action-toolkit` (Propositions 2.15(2) and 2.16), `Q ↷ E^±(Y)` is sofic
  iff each orbit `Q/Stab_Q(e)` is sofic.
* *The wreath products.* `gkp-free-generalized-wreath-soficity` (Theorem 3.7, with `K = Z`) makes
  `Z ≀^*_(E^±(Y)) Q` sofic, and `gkp-wreath-permanence-theorem` (Theorem 3.6) makes `Z ≀_(E^±(Y)) Q`
  sofic.
* *Subgroups.* Soficity passes to subgroups, which gives items 1–2.
* *Stabilizers.* `gΛ` fixes `πẽ` iff `gẽ = λẽ` for some `λ ∈ Λ`, iff `λ^(−1)g ∈ Stab_Γ(ẽ)`. So
  `Stab_Q(πẽ)` is the image of `Stab_Γ(ẽ)`, and `Stab_Γ(ẽ) ∩ Λ = 1` by freeness.

**Sanity checks.**
* `Λ = Γ`: `Q = 1`, and item 1 says `Γ = π_1(Y)` is free.
* `Λ = 1`: item 3 is vacuous, since it assumes `Q = Γ` sofic.
* `Γ = F_2 × F_2` on the Cayley tree of the first factor, with `Λ = F_2 × 1`: `Y` is a rose with
  trivial `Q`-action, and item 1 gives `F_2 × F_2 ↪ F_4 × F_2`.

∎

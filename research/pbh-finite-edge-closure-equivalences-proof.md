---
rg: 2
id: pbh-finite-edge-closure-equivalences-proof
kind: route
title: Amalgams become HNN extensions of the product, HNN extensions become conjugacy, conjugacy becomes a swap of commuting copies in the wreathed square, and the swap is one finite amalgam
target: pbh-finite-edge-closure-equivalences
requires:
  - free-permutational-products-preserve-pbh
  - boone-higman-type-a-class-closed-under-finite-extensions
  - aut-free-groups-satisfy-permutational-boone-higman
---

Lane proof (bh-free-10, 2026-09-18), not reviewed. Numbers refer to the forms in the target.
The cycle is (1) ⟹ (5) ⟹ (4) ⟹ (2) ⟹ (1), together with (1), (2) ⟺ (3).

**(2) ⟹ (4).** Take `L = G*_θ` and `s = t`.

**(4) ⟹ (2).** By Part 5 of `free-permutational-products-preserve-pbh-proof`, `G*_θ`
embeds in `L *_(C_2) (C_2 × ⟨u⟩)` by `t -> u s`. That group is in `B_A` by Part 3 there.

**(2) ⟹ (1).** Let `i: C -> X` and `j: C -> Y`.
- `X × Y ∈ B_A` (`boone-higman-type-a-class-closed-under-finite-extensions`). Let
  `φ: i(C) × 1 -> 1 × j(C)` send `(i(c), 1)` to `(1, j(c))`.
- Map `X *_C Y -> (X × Y)*_φ` by `x -> (x, 1)` and `y -> t^(-1) (1, y) t`. On `C` the two
  maps agree: `t^(-1) (1, j(c)) t = (i(c), 1)`.
- **Injectivity.** Take a reduced alternating word in `X \ i(C)` and `Y \ j(C)`, of length
  at least 2. Its image alternates between `(x, 1)` and `t^(-1) (1, y) t`.
  - A pinch `t (x, 1) t^(-1)` would need `(x, 1) ∈ i(C) × 1`.
  - A pinch `t^(-1) (1, y) t` would need `(1, y) ∈ 1 × j(C)`.
  - Neither occurs, so by Britton's lemma the image is nontrivial.
- By (2), `(X × Y)*_φ ∈ B_A`, hence so is `X *_C Y`.

**(1) ⟹ (5).** (5) is an instance of (1), since `A_1 × A_2` is finite.

**(5) ⟹ (4).** Let `C_1, C_2 ≤ G` be finite and `θ: C_1 -> C_2`.
- `H = (G × G) ⋊ ⟨σ⟩ ∈ B_A`, with `σ` the swap, as a finite-index overgroup of `G × G`.
- `A_1 = C_1 × 1` and `A_2 = 1 × C_2` commute and meet trivially. Take `θ'(c, 1) = (1, θ(c))`.
- By (5), `L = H *_(A_1 × A_2) (A_1 × A_2) ⋊ ⟨e⟩ ∈ B_A`. In `L`,
  `e (c, 1) e^(-1) = (1, θ(c))` and `σ (1, θ(c)) σ^(-1) = (θ(c), 1)`.
- So `s = σ e` conjugates `C_1 × 1` to `C_2 × 1` along `θ`, inside `G × 1 ≅ G`.

**(1) and (2) ⟹ (3).** Choose a maximal tree. Adjoin the vertex groups one leaf at a time,
each by an amalgam over a finite edge group; the vertex groups are in `B_A`, and (1)
applies at each step. Then adjoin the remaining edges, each by an HNN extension over finite
subgroups of the current group; (2) applies at each step.

**(3) ⟹ (1), (2).** Amalgams and HNN extensions are graphs of groups with one edge.

## The finite-quotient case

Suppose `q: G -> Q` has finite image and is injective on `C_1 ∪ C_2`.
- Then `θ̄ = q θ q^(-1): q(C_1) -> q(C_2)` is defined, and `q` extends to
  `G*_θ -> Q*_θ̄`. The target is an HNN extension of a finite group, hence virtually free.
- Let `P` be the preimage of a free finite-index subgroup. On each conjugate of `C_1` the
  map is injective, and a finite subgroup of a free group is trivial. So `P` meets every
  edge stabilizer of the Bass–Serre tree of `G*_θ` trivially.
- `P` has finite index, so it has finitely many orbits of vertices and edges. By Bass–Serre
  theory, `P` is a free product of finitely many vertex stabilizers `P ∩ gGg^(-1)` and a
  finitely generated free group.
- Each factor is in `B_A`. So `P ∈ B_A` by BFFHZ Corollary F
  (`aut-free-groups-satisfy-permutational-boone-higman`), and `G*_θ ∈ B_A` by finite-index
  overgroup closure. `∎`

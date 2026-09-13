---
rg: 2
id: radu-edge-coset-action-sofic-from-frame-dynamics-microstates
kind: route
title: Label framed edge neighbourhoods of the second tree by their images in finite graph quotients, and transport microstates of the frame dynamics
target: radu-edge-coset-action-is-sofic
requires:
  - homogeneous-quotient-soficity-gives-vertex-soficity
  - radu-edge-stabilizer-is-second-prime-congruence-subgroup
  - radu-second-prime-frame-dynamics-admit-microstates
---

# Derivation

**Setup.** Apply item 1 of `homogeneous-quotient-soficity-gives-vertex-soficity` with
* `L = PB^×(F_(𝔮')) ≅ PGL_2(Q_2)`, totally disconnected, locally compact and second countable;
* `K = K_χ = Fix_L(N(e'))`, which is compact open;
* `A = ρ(Q) ≅ Q`, which is countable;
* `C = A ∩ K = C_χ`, by `radu-edge-stabilizer-is-second-prime-congruence-subgroup`.

**The lattice tower.**
* *Existence.* Torsion-free cocompact lattices `Λ_1 ≤ PGL_2(Q_2)` exist, for instance the Ihara
  Schottky lattices: free groups acting freely and cocompactly on the 3-regular tree.
* *Tower.* `Λ_1` is finitely generated linear, hence residually finite. The intersections of its
  subgroups of index at most `N` form a normal tower with trivial intersection.

**Conclusion.**
* *Microstates.* By `radu-second-prime-frame-dynamics-admit-microstates`, applied to each `Λ_N`, the
  hypothesis `(HV1)` holds for every `N`, every finite `F` and every `ε`.
* *Soficity.* Item 1 of the principle gives that `A ↷ A/C` is sofic, i.e. `Q ↷ Q/C_χ`, which is
  `radu-edge-coset-action-is-sofic`.

**The label, concretely.** For a frame `gΛ_N ∈ L/Λ_N` and a framed edge neighbourhood `x ∈ L/K_χ`,
the label `Λ_N g^(−1) x` is the image of `x` in the finite 3-regular graph `Λ_N\T'`, seen through
the frame. Once the girth of `Λ_N\T'` exceeds the diameter of a window, distinct framed
neighbourhoods in the window get distinct labels at every frame. Only the microstates have to be
built; the separation is exact.

∎

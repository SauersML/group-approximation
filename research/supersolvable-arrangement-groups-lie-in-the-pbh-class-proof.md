---
rg: 2
id: supersolvable-arrangement-groups-lie-in-the-pbh-class-proof
kind: route
title: Climb Terao's tower; rank-one fibres split off Z and fibres of rank at least two are absorbed by free-kernel permanence
target: supersolvable-arrangement-groups-lie-in-the-pbh-class
requires:
  - free-kernel-extensions-stay-in-the-permutational-class
  - aut-free-groups-satisfy-permutational-boone-higman
  - boone-higman-type-a-class-closed-under-finite-extensions
  - type-a-action-gives-boone-higman-for-subgroups
---

**Input** (Terao 1986; Falk--Randell 1985; cited, not read). A supersolvable
arrangement is fiber-type. There is a tower of linear projections
`M_ℓ -> M_(ℓ−1) -> … -> M_1`, where each `M_i` is the complement of an arrangement
`A_i` in `C^i` and each map is the restriction of a linear projection `C^i -> C^(i−1)`.
The map is a locally trivial fibration with fibre `C` minus `d_i` points. The
hyperplanes of `A_i` not containing the kernel direction are graphs of affine maps
`C^(i−1) -> C`. The base `M_1` is `C` minus `d_1` points.

**Induction.** We show `π_1(M_i) ∈ B_A`, and that `M_i` is aspherical.

- **Base.** `M_1 = C` minus `d_1` points. It is aspherical and
  `π_1 = F_(d_1) ≤ F_2 ≤ Aut(F_2) ∈ B_A`. For `d_1 = 0` it is trivial.
- **`d_i = 0`.** `M_i = M_(i−1) × C`.
- **`d_i = 1`.** The single transverse hyperplane is the graph of an affine map
  `f: C^(i−1) -> C`. Then `(x, t) ↦ (x, t − f(x))` identifies `M_i` with
  `M_(i−1) × C^×`, so `π_1(M_i) = π_1(M_(i−1)) × Z`. It lies in `B_A` by closure under
  products (`Z ≤ Aut(F_2)`).
- **`d_i >= 2`.**
  - The fibre is aspherical and so is the base, so `M_i` is aspherical.
  - `π_2(M_(i−1)) = 0`, and the homotopy sequence gives
    `1 -> F_(d_i) -> π_1(M_i) -> π_1(M_(i−1)) -> 1`.
  - Part 1 of `free-kernel-extensions-stay-in-the-permutational-class` applies.

**Envelope.** `π_1(M_ℓ)` is finitely generated. Every finitely generated group in
`B_A` embeds in a finitely presented simple group and has solvable word problem
(`type-a-action-gives-boone-higman-for-subgroups`). ∎

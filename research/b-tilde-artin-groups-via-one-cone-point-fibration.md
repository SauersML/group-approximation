---
rg: 2
id: b-tilde-artin-groups-via-one-cone-point-fibration
kind: claim
title: Moving the two special points of the B̃_n orbifold into the configuration gives a punctured-curve bundle over Conf_(n+1)(C), a second proof that every A(B̃_n) lies in B_A
distinct_from:
  b-tilde-artin-groups-satisfy-permutational-boone-higman: that proves the same membership through Li--Roushon's fibration of a Möbius-transformed arrangement over a configuration space of C^×, which needs n >= 3 and Thom's isotopy lemma; this uses an explicit branched-cover bundle over Conf_(n+1)(C), valid for every n >= 1, with a fibre of smaller rank.
  euclidean-artin-toric-commensurability: that reduces Euclidean Artin groups to toric arrangement groups; this fibres the B_n toric complement after crossing it with Conf_2(C).
  weyl-toric-arrangements-b-d-e-f-are-not-fiber-type: that says no toric projection fibres the B_n arrangement; the bundle here is not a toric projection.
artifacts:
  - research/artifacts/gq-bh-bh-verify-artin-euclidean-toric.md
---

**ESTABLISHED** through `b-tilde-artin-groups-via-one-cone-point-fibration-proof`. This
is a lane proof, elementary, and not independently reviewed. No priority is claimed.
The conclusion is already on main; the construction is the point.

## Statement

For `n >= 1`, put `N_B = {v ∈ (C^×)^n : v_i ≠ v_j^(±1) for i ≠ j, and v_k ≠ 1}`, the
B_n toric Weyl complement with lattice `Z^n`. Let

    E° = {(c_1, c_2, x, y) : c_1 ≠ c_2; x ∈ Conf_n(C); x_k ≠ c_1 for all k;
          y_k^2 = (x_k − c_1)(x_k − c_2) for all k}.

1. `E° ≅ Conf_2(C) × N_B`, so `π_1(E°) ≅ Z × π_1(N_B)`.
2. `(c_1, c_2, x, y) ↦ (c_1, x_1, …, x_n)` is a fibre bundle `E° -> Conf_(n+1)(C)`.
   - Its fibre `Σ` is the connected `(Z/2)^n`-cover of `C − {c_1}` (the `c_2`-line)
     branched exactly over `x_1, …, x_n`.
   - `π_1(Σ)` is free of rank `1 + n·2^(n−1)`.
3. Hence `1 -> F_(1+n·2^(n−1)) -> Z × π_1(N_B) -> P_(n+1) -> 1`, and
   `Z × π_1(N_B) ∈ B_A` (`free-kernel-extensions-stay-in-the-permutational-class`).
4. So `π_1(N_B) ∈ B_A`, and `A(B̃_n) ∈ B_A` for every `n >= 2`
   (`euclidean-artin-toric-commensurability`, with `L = Z^n = P^∨(B_n)`). Here
   `B̃_2 = C̃_2`.

## Picture

In Allcock's picture the B̃_n orbifold is the plane with one puncture and one cone
point of order 2. Here the puncture `c_1` and the cone point `c_2` become moving
points.
- The strands and the puncture form a configuration in `C`: they must avoid each
  other.
- The cone point `c_2` may sit on strands. It is the fibre coordinate, and strand `k`
  at the cone point is a simple branch point of the fibre.
- Two strands can never be at the cone point simultaneously, so the branch points
  never collide.

This is exactly what fails for D̃_n, where both special points are cone points
(`d-tilde-artin-groups-satisfy-permutational-boone-higman`).

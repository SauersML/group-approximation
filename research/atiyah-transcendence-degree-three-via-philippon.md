---
rg: 2
id: atiyah-transcendence-degree-three-via-philippon
kind: route
title: Run the cycle argument in three variables, violate the cycle inequality with the Chow form of Philippon's approximating zero-cycle, and climb finite extensions by continuity on threefolds
target: atiyah-base-change-in-transcendence-degree-three-under-det
requires:
  - atiyah-base-change-in-transcendence-degree-two-under-det
  - points-of-c3-approximable-by-zero-cycles
  - atiyah-cycle-machinery-transcribes-to-three-variables
artifacts:
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part2.md
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part4.md
---

This is the case `s = 3` of `full-atiyah-base-change-via-cycle-approximation`,
with its Diophantine requirement now proved.

* **Purely transcendental case.**
  - **Setup.** Let `z in C^3` have algebraically independent coordinates, and
    let `A` be a matrix over `Qbar[G][x_1, x_2, x_3]` with excess
    `kappa > 0` at `z`.
  - **Reduction.** By [[atiyah-cycle-machinery-transcribes-to-three-variables]]
    (items 1-2) there is a full pencil `M = M_0 + sum_(i<=3) x_i M_i` over
    `Z[G]` with `kappa_0 >= 1` at `z`, and a proper closed `Y` over `Q` with
    `z notin Y`.
  - **Cycle inequality.** By item 3, every integral product `F` of linear
    forms at affine points of `A^3` satisfies
    `a(F) + (B-1) b(F) + C deg F >= 0`, with `B = N/kappa_0`.
  - **Contradiction.** [[points-of-c3-approximable-by-zero-cycles]] supplies an
    `F` with `a(F) + (B-1) b(F) + C deg F < 0`. So `kappa_0 = 0`, which gives
    Strong Atiyah over `Qbar(z_1, z_2, z_3)`.
  - **Points at infinity and components in `Y`.** They are absorbed by
    Corollary 6 once the hyperplane at infinity is added to `Y`.
* **Finite extensions.** Use item 4 of the transcription claim, which is
  Part 4, Section 7, on threefolds:
  - Noether normalization onto `A^3`, finite étale off `V(g)`;
  - fibre sums equal the generic value off `Y` at algebraic points and at
    generic points;
  - at points of transcendence degree 1 or 2 they are handled by
    [[atiyah-base-change-in-transcendence-degree-two-under-det]] applied to the
    `Qbar`-closure of the point;
  - upper semicontinuity gives continuity, and density plus connectedness give
    constancy.
* **Galois invariance.** It follows as in Theorem 5, item 2, because the
  kernel dimension is the generic rank value.

The route does not fire until the transcription claim is established.

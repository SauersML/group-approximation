---
rg: 2
id: full-atiyah-base-change-via-cycle-approximation
kind: route
title: Run the two-variable cycle argument in s variables, violate the cycle inequality with approximating zero-cycles, and climb finite extensions by continuity
target: determinant-conjecture-gives-full-atiyah-base-change
requires:
  - atiyah-base-change-in-transcendence-degree-two-under-det
  - determinant-conjecture-bounds-determinants-over-galois-orbits
  - algebraically-independent-points-approximable-by-zero-cycles
artifacts:
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part1.md
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part2.md
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part4.md
---

Induct on `s = trdeg F`. The cases `s <= 2` are
[[atiyah-base-change-in-transcendence-degree-two-under-det]].

* **Jump locus in `s` variables.** Normal form over
  `D(x_1..x_(s-1))[x_s]`, with constant-term evaluation in iterated Laurent
  series. This puts algebraic jumps inside a proper closed `Y` over `Q`, and the
  generic rank bounds the kernel everywhere. The proof is Part 1, Section 1,
  with `x_1` replaced by `x' = (x_1..x_(s-1))`. The finitely many bad central
  roots become a proper closed set of `A^(s-1)`, again by the coordinate trick.
* **Reduction.** (R1')-(R3') give a full pencil
  `M = M_0 + sum_i x_i M_i` over `Z[G]` with `kappa_0 >= 1` at a point `z` with
  algebraically independent coordinates.
* **Cycle inequality.** Use `Lambda_k = span {zeta^alpha : |alpha| <= k}` and
  `s` multiplication maps. The unit-valued norm form now has `s + 1` variables,
  using `F_(q^(s+1))`. Proposition S uses
  `||S_theta^T (1, zeta)|| >= c ||zeta - z||`. This is the `s`-variable form of
  [[determinant-conjecture-bounds-determinants-over-galois-orbits]], and every
  integral Chow-type form satisfies
  `a(F) + (B-1) b(F) + C deg F >= 0`, with `B = N/kappa_0`.
* **Contradiction.** [[algebraically-independent-points-approximable-by-zero-cycles]]
  supplies a violating `F`. So `kappa_0 = 0`, which gives Strong Atiyah over
  `Qbar(z_1..z_s)`.
* **Finite extensions.** Part 4, Section 7, verbatim in dimension `s`:
  - Noether normalization onto `A^s`, finite étale off `V(g)`;
  - fibre sums equal the generic value off `Y`, at algebraic points, at points
    of intermediate transcendence degree (induction hypothesis on the
    `Qbar`-closure of the point), and at generic points;
  - upper semicontinuity gives continuity, and density plus connectedness give
    constancy.

The `s`-variable versions of Parts 1-2 are routine transcriptions and not yet
written out. The route does not fire, because its Diophantine requirement is
open.

---
rg: 2
id: atiyah-base-change-in-transcendence-degree-two-under-det
kind: claim
title: Under the determinant conjecture, Strong Atiyah over Qbar extends to Qbar(z_1, z_2) for algebraically independent complex z_1, z_2
distinct_from:
  atiyah-base-change-in-transcendence-degree-one-under-det: that covers coefficient fields of transcendence degree at most one, by continuity along curves; this covers purely transcendental fields of transcendence degree two, through integral models of zero-dimensional cycles.
  determinant-conjecture-gives-full-atiyah-base-change: that is the statement for all complex coefficients; this is its purely transcendental degree-two case, with transcendence degree three and algebraic extensions still open.
artifacts:
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part1.md
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part2.md
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part3.md
---

**ESTABLISHED (unreviewed)** by [[atiyah-transcendence-degree-two-proof]].

Let `G` be torsion-free and satisfy Strong Atiyah over `Qbar` and Lueck's
determinant conjecture. Put `D = D_(Qbar[G])`. Let `z_1, z_2 in C` be
algebraically independent over `Qbar`.

1. For every `m x n` matrix `A` over `Qbar[G][x_1, x_2]`,
   `dim_G ker A(z_1, z_2) = n - rk_(D(x_1)(x_2)) A`. So every matrix over
   `Qbar(z_1, z_2)[G]` has integral von Neumann kernel dimension.
2. These dimensions are the same for all algebraically independent pairs. This
   is Galois invariance for automorphisms of `C` fixing `Qbar`, among such
   pairs.

**Not covered.**
- Finite extensions of `Qbar(z_1, z_2)`. These should follow as in
  transcendence degree one, from constant fibre sums off the jump locus, but
  that is not written out.
- Transcendence degree at least three.

**The mechanism.** Minkowski's theorem gives a bivariate integer polynomial of
degree `n` with value about `H^(-n^2/4)` at `z`. One of its irreducible factors
has the same exponent. A univariate polynomial small at `z_1` is automatically
coprime to it, so their joint zero cycle is zero-dimensional, with no
transversality condition. The Sylvester identity shows that its Chow form is
small on all hyperplanes through `z`. The determinant conjecture, applied once
to the integral model of the cycle, forbids a kernel at `z`.

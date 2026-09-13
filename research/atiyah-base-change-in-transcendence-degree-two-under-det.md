---
rg: 2
id: atiyah-base-change-in-transcendence-degree-two-under-det
kind: claim
title: Under the determinant conjecture, Strong Atiyah over Qbar extends to every coefficient field of transcendence degree at most two
distinct_from:
  atiyah-base-change-in-transcendence-degree-one-under-det: that covers coefficient fields of transcendence degree at most one, by continuity along curves; this covers transcendence degree two, through integral models of zero-dimensional cycles and then continuity on surfaces.
  determinant-conjecture-gives-full-atiyah-base-change: that is the statement for all complex coefficients; this is its case of transcendence degree at most two, and degree three and up stays open.
artifacts:
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part1.md
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part2.md
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part3.md
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part4.md
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
3. **(Theorem 6, Part 4.)** For every field `F ⊂ C` with
   `trdeg_(Qbar) F <= 2`, every matrix over `F[G]` has integral kernel
   dimension, invariant under automorphisms of `C` fixing `Qbar`.

**Not covered.** Transcendence degree at least three. The machinery of Parts
1-2 carries over to `A^s`. What is missing is a violating Chow-type form
(Part 4, Section 8).

**The mechanism.** Minkowski's theorem gives a bivariate integer polynomial of
degree `n` with value about `H^(-n^2/4)` at `z`. One of its irreducible factors
has the same exponent. A univariate polynomial small at `z_1` is automatically
coprime to it, so their joint zero cycle is zero-dimensional, with no
transversality condition. The Sylvester identity shows that its Chow form is
small on all hyperplanes through `z`. The determinant conjecture, applied once
to the integral model of the cycle, forbids a kernel at `z`.

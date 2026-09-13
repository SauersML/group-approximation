---
rg: 2
id: atiyah-transcendence-degree-one-proof
kind: route
title: Push the one-variable base change along a finite map from a curve and conclude by continuity and density of algebraic points
target: atiyah-base-change-in-transcendence-degree-one-under-det
requires:
  - determinant-conjecture-gives-one-variable-atiyah-base-change
  - atiyah-base-change-holds-off-a-countable-set
artifacts:
  - research/artifacts/atiyah-transcendence-degree-one-base-change-2026-09-13.md
---

The complete argument is in `research/artifacts/atiyah-transcendence-degree-one-base-change-2026-09-13.md`,
Section 8 (Theorem 4 and Corollary 5).

* **Item 1.** Take `F = Qbar(C)` for a smooth affine curve `C`, embedded through a
  transcendental point, and clear denominators by a regular function nonzero
  there. Choose a finite map `x: C -> A^1`, so that `Qbar[C]` is free of rank `e`
  over `Qbar[x]`.
  - Restriction of scalars gives a family `rho(M)` over `Qbar[G][x]`. At
    unramified `z` it is conjugate by an invertible scalar matrix to the direct
    sum over the fibre.
  - [[determinant-conjecture-gives-one-variable-atiyah-base-change]], together
    with the finiteness of algebraic jumps, makes
    `sum_(x(P) = z) dim ker M(P) = K` for `z` outside a finite set `Z_0`.
  - `k(P) = dim ker M(P)` is upper semicontinuous in `P`. For `P'` near `P`, the
    other fibre points of `x(P')` are near those of `x(P)`. So
    `k(P') = K - sum_(i >= 2) k(P'_i) >= k(P) - (e-1) eps`, and `k` is lower
    semicontinuous on `C° = C \ x^-1(Z_0)`.
  - Algebraic points of `C°` are dense and carry integer values (Strong Atiyah
    over `Qbar`). So the continuous `k` is integer-valued, locally constant, and
    constant on the connected `C°`, which contains every transcendental point.
  - Automorphisms of `C` fixing `Qbar` permute the transcendental points, which
    gives the invariance.
* **Item 2.** Write `C = U B^-1 V` over `D` with `B` invertible in `U(G)`. The
  Schur complement turns `ker(z - C)` into the kernel of the family
  `[[B, V], [U, x I]]` at `z`. A transcendental eigenvalue would lie in `E_G` of
  [[atiyah-base-change-holds-off-a-countable-set]], which the one-variable
  theorem makes empty.
* **Item 3.** An element `d in D ∩ C` with `d = z` transcendental is an
  eigenvalue of the `1 x 1` matrix `d`, so item 2 applies. QED

---
rg: 2
id: one-variable-atiyah-base-change-proof
kind: route
title: Reduce to an integral pencil, apply the determinant conjecture to companion models, and beat the box principle
target: determinant-conjecture-gives-one-variable-atiyah-base-change
requires:
  - atiyah-base-change-holds-off-a-countable-set
  - determinant-conjecture-excludes-liouville-atiyah-exceptions
artifacts:
  - research/artifacts/atiyah-one-variable-base-change-2026-09-12.md
---

The complete argument is in `research/artifacts/atiyah-one-variable-base-change-2026-09-12.md`.

* **Section 1: reduction.** Suppose the excess is `kappa > 0` at a transcendental
  `z_0`.
  - Higman linearization gives a linear pencil with the same excess.
  - Padding with 0-1 coordinate blocks gives a square pencil, full over `D(x)`,
    whose excess is at least `kappa`. This uses the dimension formula for
    intersections of `U(G)`-submodules.
  - Restriction of scalars from `O_F` adds the nonnegative excesses of the
    conjugate pencils. Nonnegativity is the normal form of
    [[atiyah-base-change-holds-off-a-countable-set]]. Pad once more.
  - Only finitely many algebraic parameters are jumps (item 1 of
    [[determinant-conjecture-excludes-liouville-atiyah-exceptions]]).
* **Section 2: resultant identity.** For irreducible `p` avoiding the jump
  polynomials, the companion pencil `(E, F)` has `det(xE - F) = p` and
  `E^-1 F = V diag(alpha_j) V^-1`. So `X = M_0 (x) E + M_1 (x) F` over `Z[G]` is
  similar by invertible scalars to `(+)_j M(alpha_j)`, and
  `Delta(X) = |a|^N prod_j Delta(M(alpha_j))`.
* **Section 3: upper bound.** Min-max near the kernel point `z_0` (Lemma 2 of
  the Liouville artifact) gives
  `Delta(M(alpha)) <= C_0 |alpha - z_0|^(kappa_0) max(1,|alpha|)^(N - kappa_0)`.
* **Section 4: polynomial inequality.** The determinant conjecture gives
  `Delta(X) >= 1`, hence `|p(z_0)| >= C_0^(-n/kappa_0) M(p)^(-(N - kappa_0)/kappa_0)`.
* **Section 5: box principle.** Pigeonholing `(H+1)^(n+1)` integer polynomials
  gives `P_H` with `|P_H(z_0)| <= c H^(-w)`, where `w = n` for real `z_0` and
  `w = (n-1)/2` for complex `z_0`. Factor `P_H` into irreducibles, using
  `M(P_H) <= (n+1)^(1/2) H`, and apply Section 4 to each factor. This forces
  `w <= (N - kappa_0)/kappa_0` for all `n`, which is impossible. So `kappa = 0`,
  and `E_G` is empty.

Items 1-3 of the target then follow from items 2-3 of
[[atiyah-base-change-holds-off-a-countable-set]]. QED

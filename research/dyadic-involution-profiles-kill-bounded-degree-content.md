---
rg: 2
id: dyadic-involution-profiles-kill-bounded-degree-content
kind: claim
title: A dyadically invariant involution profile forces every bounded-degree polynomial piece of an SL_N(F_2) rank model to be trivial
distinct_from:
  matrix-unit-root-rank-models-of-simple-el3-are-trivial: that propagates matrix-unit shape of the six unit root elements of SL_3(F_2) to every root subgroup of EL_3 over a simple non-directly-finite ring; this is a finite-group statement at one level group SL_N(F_2), excluding orthogonal pieces of bounded polynomial degree from the involution displacement profile alone.
  free-rank-models-on-sl3-admit-no-block-support: that shows free SL_3(F_p) content forces a positive rank of the product of two unit root displacements; this excludes bounded-degree polynomial content at level groups and records that projective content has the same involution profile as free content.
  leavitt-el3-rank-models-over-finite-fields-are-trivial: that is the open triviality of every rank model of the Leavitt EL_3; this excludes one family of level-group shapes, given the dyadic profile identity.
artifacts:
  - research/artifacts/level-group-polynomial-content-2026-09-12.md
---

**ESTABLISHED** (proof in the artifact, Sections 1–4). `gk-vf-linear` passed it (Section 39 of
`research/artifacts/gk-vf-linear-verification-2026-09-12.md`, ead15402a3). The pass covers the
polynomial Jordan count, additivity over orthogonal pieces, the projective profile `1/2`, and the
dyadic identity for flag diagonals. Let `k` be a field of characteristic
`2`, `M` a ring with a faithful normalized Sylvester rank function, `N >= 4(D + 1)`,
`H = SL_N(F_2)` and `sigma : H -> M^x` a homomorphism. Write `f(r) = rk(sigma(g_r) - 1)` for an
involution `g_r = 1 + n` with `n^2 = 0` and `rank n = r`. Suppose:

* `1 = sum_i e_i` is a finite orthogonal decomposition into idempotents commuting with
  `sigma(H)`. On each corner `e_i M e_i ~= M_(d_i)(k) (x) C_i`, `sigma` acts as `rho_i (x) 1`,
  where `rho_i` is trivial, projective, or `F_i(V_N, V_N*)` for a strict polynomial bifunctor
  `F_i` of total degree at most `D`;
* `f(2r) = f(r)` for every integer `1 <= r <= N/4`.

Then every polynomial `rho_i` is trivial.

**Proof idea.**
* **Lemma.** On `F(V_N, V_N*)` the displacement rank of `g_r` is a polynomial in `r` of degree at
  most `D` with value `0` at `r = 0`. It counts `J_2` blocks in the weight decomposition over the
  Jordan summands of `V_N`.
* **Projective pieces** contribute the constant `1/2`.
* **Rigidity.** The dyadic identity at `D + 1` integers forces the polynomial part of the profile
  to vanish. Transvections, which generate `SL_N(F_2)`, then act trivially on every polynomial
  piece.

**Covered shapes.** Natural, dual, natural-plus-dual, adjoint `V (x) V*`, and tensor, exterior,
symmetric and divided powers of bounded degree, each with free and trivial complements.

**Not covered.**
* Projective and free content, whose profile is constant.
* Pieces of degree growing with `N`.
* Restrictions that do not split orthogonally.

**Leavitt instance.** For `R = L_K(1,2)` with `char K = 2`, Proposition 2 of
`research/artifacts/el3-rank-ring-rigidity-2026-09-12.md` supplies the dyadic identity on every
level group `SL_(3·2^(k+1))(F_2)` inside `R^x`. So no char-two rank model of `R^x` has a nonzero
bounded-degree polynomial piece at a level group with orthogonal trivial, projective and
polynomial complements (artifact Section 5).

---
rg: 2
id: filtered-matrix-unit-rank-models-of-simple-el3-are-trivial
kind: claim
title: Rank models of EL_3 over a simple non-directly-finite ring with a finite triangular flag of matrix-unit pieces are trivial
distinct_from:
  matrix-unit-root-rank-models-of-simple-el3-are-trivial: that needs the unit root elements to act by matrix units on the whole model, with a complement they kill; this glues finitely many such pieces by arbitrary triangular extension terms, including non-split extensions of the natural module by trivial ones in either order, and allows transposed pieces.
  matrix-unit-root-rank-models-of-odd-char-simple-el3-are-trivial: that is the odd-characteristic single-piece theorem; this glues finitely many pieces of the characteristic-p types along a triangular flag.
  el3-rank-models-factor-through-ring-rank-models: that asserts triviality of every rank model, with no flag or block hypothesis; this proves it only for finite triangular extensions of matrix-unit, transposed matrix-unit and trivial pieces, and leaves two-sided mixing, other composition factors and diffuse flags open.
artifacts:
  - research/artifacts/el3-rank-model-extensions-2026-09-12.md
---

Let `p` be a prime and `R` a simple unital algebra over a field of characteristic `p` that is
not directly finite, for instance `L_K(1,n)` with `char K = p` and `n >= 2`. Let `M` be a rank
ultraproduct over a field of characteristic `p`, and `sigma : EL_3(R) -> M^x` a homomorphism.
Suppose there is a finite decomposition `1 = h_1 + ... + h_m` into orthogonal idempotents
such that:
* `sigma` is upper triangular: `h_s sigma(g) h_r = 0` for `s > r`;
* each graded piece `sigma_t = h_t sigma h_t` is one of three kinds:
  - a **matrix-unit piece**: orthogonal idempotents `p_1, p_2, p_3` in `h_t M h_t` with
    `sigma_t(x_ij(1)) = h_t + u_ij`, `u_ij` in `p_i M p_j`, `u_ij u_jk = u_ik`,
    `u_ij u_ji = p_i`;
  - a **trivial piece**;
  - a **transposed piece**: `sigma_t o theta^-1` is a matrix-unit piece for `EL_3(R^op)`,
    where `theta(g) = (g^T)^-1` sends `x_ij(a)` to `x_ji(-a)`, for instance the dual natural
    module.

Then `sigma` is trivial.

This covers the surviving shape named by lane `gk-l-gate-neg` in its triangular form:
* non-split extensions `0 -> trivial -> W -> natural -> 0` and `0 -> natural -> W -> trivial -> 0`;
* finite towers of natural, dual natural, multiplicity and trivial layers;
* complements whose extension terms run in one direction along some finite ordering.

What survives is recorded in artifact Section 3: two-sided mixing, other composition factors,
and diffuse flags.

**ESTABLISHED** by `filtered-matrix-unit-rank-models-proof` (artifact Section 2, Theorem 2).

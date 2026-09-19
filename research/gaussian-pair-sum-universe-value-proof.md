---
rg: 2
id: gaussian-pair-sum-universe-value-proof
kind: route
title: Richness from the P-free law of Gaussian pair sums, SDP convergence by the law of large numbers for the Gram matrix, and the value bound by running the five reduction steps in the Gaussian model and inserting Theorem G
target: gaussian-pair-sum-universe-rich-2to1-game-has-vanishing-value
requires: [gaussian-pair-resampling-partitions-are-unstable]
artifacts:
  - experiments/gaussian-pair-sum-universe-2026-09-17/check_gaussian_universe.py
---

Notation as in the target. `mu` is the law of `X`, `T_P f = E[f(X) | Pi_P X]`
on `L^2(mu)`, `T = E_P T_P`, `s = sum_a x_a`.

## Item 1 (richness)

For fixed `P`, `y_b = x_a + x_a'` over disjoint pairs, so the `y_b` are
independent `N(0, 2 I_d / d)`. The law of `Y` given `P` is the same for every
`P`. Hence `Pr[P | Y] = Pr[P]` is uniform, and `Pr[P | X]` is uniform because
`P` is independent of `X`.

## Item 2 (SDP)

Fix `n` and let `d >= 2n`; then `X` and `Y` have full row rank a.s., so `U(X)`
and `U(Y)` have orthonormal rows. Hence `sum_a ||z(X,a)||^2 = 1`,
`<z(X,a), z(X,a')> = 0` for `a != a'`, and likewise on the right. These are the
only constraints of GKOPTW Figure 1 (quoted verbatim in the Attempts of
`rotated-frame-universe-discretises-to-robust-rich-2to1-sdp-gaps`). Each inner
product of unit vectors lies in `[-1, 1]`, so the per-edge objective
`F(X, P) = sum_a <U(X)_a, U(Y)_(P(a))> / (n sqrt2)` lies in `[-sqrt2, sqrt2]`.

As `d -> infinity`, each entry `<x_a, x_c>` of `X X^T` has mean `delta_(ac)` and
variance at most `2/d`, so `X X^T -> I` in probability, and in the same way
`Y Y^T -> 2 I`. The map `M -> M^(-1/2)` is continuous at `I`, so
`||U(X) - X||_op <= ||(X X^T)^(-1/2) - I||_op ||X||_op -> 0` and
`||U(Y) - Y / sqrt2||_op -> 0` in probability. All rows involved have norm
bounded in probability, so

`F(X, P) - sum_a <x_a, y_(P(a))> / (2n) -> 0`, and
`sum_a <x_a, y_(P(a))> = sum_a (||x_a||^2 + <x_a, x_(p_P(a))>) -> 2n`,

both in probability. So `F -> 1` in probability, and since `|F| <= sqrt2`,
`Obj_(n,d) = E F -> 1` by bounded convergence.

## Item 3 (value)

Run the five steps of `equivariant-partition-stability-reduction-proof` with
`mu` the Gaussian law. They use exactly three properties.

* **(R1) Row permutations preserve `mu` and fix `s`.** True: the rows are i.i.d.
  This gives Step 1: `rho_(A,c)(X) = Pr_sigma[A(sigma X) = sigma(c)]` is a
  fractional partition with values in `[0, 1]` and `E[rho_(A,c) | s] = 1/(2n)`.
  It also gives Step 3's claim that `sigma` maps `law(X | P, Y)` to
  `law(X | P o sigma^(-1), Y)`: `sigma` preserves `mu` and maps the fibre
  `{Pi_P X = Y}` onto `{Pi_(P o sigma^(-1)) X = Y}`.
* **(R2) `P` is uniform and independent of `X`, and of `Y`.** This is item 1.
  It is used in Steps 2 to 4.
* **(R3) `T_P` is a conditional expectation.** So it is a self-adjoint
  idempotent contraction, and `E[f(X'') | X, P] = (T_P f)(X)` when `X''` is
  drawn from `law(X | P, Y)` independently of `X`. This is used in Steps 3 to 5.

Nothing else in Steps 1 to 5 refers to frames: the Stiefel structure enters
only Step 6 (the frame-sum floor) and Step 7 (the Haar-frame SDP), which are not
used. So for every strategy pair,

`Pr[P(A(X)) = B(Y)]^4 <= 4 Stab_T(rho_A)`.

The rows here are `N(0, I_d/d)` rather than standard; rescaling `X` by
`sqrt d` commutes with every `T_P` and fixes `rho_A` up to the same rescaling,
so `Stab_T(rho_A)` is unchanged. By (R1), `rho_A` is a balanced fractional
partition in the sense of `gaussian-pair-resampling-partitions-are-unstable`,
so Theorem G gives `Stab_T(rho_A) <= ((2n)^(-kappa) + eps_n)^(1/40)`. Taking the
supremum over `(A, B)`,

`val(W_(n,d)) <= 4^(1/4) ((2n)^(-kappa) + eps_n)^(1/160)`,

for every `d >= 1`. QED.

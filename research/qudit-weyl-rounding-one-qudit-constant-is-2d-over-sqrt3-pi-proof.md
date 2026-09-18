---
rg: 2
id: qudit-weyl-rounding-one-qudit-constant-is-2d-over-sqrt3-pi-proof
kind: route
title: The commutator of the two Gram matrices of (u-1)psi and (u^*-1)psi bounds the frustration by a trace norm, and line-measurement rounding closes at 2d/(sqrt3 pi) + 4
target: qudit-weyl-rounding-one-qudit-constant-is-2d-over-sqrt3-pi
requires: []
artifacts:
  - experiments/qudit-weyl-rounding-multiqudit-2026-09-18/README.md
---

Ordinary proof, unreviewed, not Lean-verified. Lane w5-078, 2026-09-18. The numerical checks of
Lemma L and of the constants are in `experiments/qudit-weyl-rounding-multiqudit-2026-09-18/`
(`check_gram_lemma.py`).

## Setting

`d` is prime and `omega = e^(2 pi i/d)`. On one qudit `C^d`, the Weyl operators `D(v)`, `v in F_d^2`,
satisfy `D(v) D(v') = omega^([v,v']) D(v') D(v)`, where `[.,.]` is the symplectic form. The nonzero
vectors fall into `d+1` lines through `0`. Two Weyl operators commute iff their vectors lie on a
common line (or one of them is `0`).

Write `K = c_0 I + sum_j |c_j| u_j`, where `u_j = (c_j/|c_j|) g_j` and each `g_j` is a non-identity
Weyl operator, and `W = sum_(j>=1) |c_j|`. (The identity term shifts `lambda_max` and every
`<phi|K|phi>` equally, and it does not change `W - lambda_max`. So we drop it.) Let `psi` be a top
eigenvector. Put `delta_j = 1 - Re<psi|u_j|psi> in [0,2]`, so that
`lambda_max = sum_j |c_j|(1 - delta_j)` and `F := W - lambda_max = sum_j |c_j| delta_j`. Let `l(j)` be
the line of `g_j`.

## Lemma L (commutator-Gram uncertainty inequality)

Let `u_1, ..., u_k` be unitaries on any Hilbert space with `u_i u_j = omega^(t_ij) u_j u_i`, where
`t_ij in Z/d`. Let `psi` be a unit vector, `w in R_{>=0}^k` and `D = diag(sqrt w_i)`. Put
`delta_i = 1 - Re<u_i>`, `z_ij = <u_i^* u_j>` and `C_ij = (1 - omega^(t_ij)) z_ij`, where
`<X> = <psi|X|psi>`. Then `C` is Hermitian with zero diagonal, and

```text
(L1)   sum_i w_i delta_i  >=  ||D C D||_1 / 4 ;
(L2)   sum_i w_i delta_i  >=  ( sum_(i<j) w_i w_j sin^2(pi t_ij/d) |z_ij|^2 )^(1/2) ;
(L3)   |z_ij|  >=  1 - (sqrt delta_i + sqrt delta_j)^2 .
```

*Proof.* Let `a_i = (u_i - 1)psi` and `b_i = (u_i^* - 1)psi`. Define `H_ij = <a_i, a_j>` and
`B_ij = <b_j, b_i>`. `H` is a Gram matrix, and `B` is the transpose of the Gram matrix of the `b_i`.
So both are positive semidefinite. Their diagonals are `||(u_i - 1)psi||^2 = 2 delta_i` and
`||(u_i^* - 1)psi||^2 = 2 - 2 Re<u_i^*> = 2 delta_i`. Next,

```text
H_ij - B_ij = <(u_i^* - 1)(u_j - 1)> - <(u_j - 1)(u_i^* - 1)> = <u_i^* u_j - u_j u_i^*> .
```

Conjugating `u_i u_j = omega^(t_ij) u_j u_i` by `u_i^*` on both sides gives
`u_j u_i^* = omega^(t_ij) u_i^* u_j`. So `H - B = C`. Then `DCD = DHD - DBD` is a difference of two
positive semidefinite matrices, each with trace `T := 2 sum_i w_i delta_i`. If `P` is the spectral
projection onto the positive part of `DCD`, then
`tr (DCD)_+ = tr P DHD P - tr P DBD P <= tr DHD = T`. The same bound holds for `tr (DCD)_-`. So
`||DCD||_1 <= 2T`, which is (L1).

For (L2): `DCD` is Hermitian with trace `0`. Let `p = tr (DCD)_+ = tr (DCD)_-`. Then
`||DCD||_F^2 = sum lambda_+^2 + sum lambda_-^2 <= p^2 + p^2`, so `||DCD||_1 = 2p >= sqrt2 ||DCD||_F`.
Also `||DCD||_F^2 = 2 sum_(i<j) w_i w_j |1 - omega^(t_ij)|^2 |z_ij|^2` and
`|1 - omega^t| = 2|sin(pi t/d)|`. Substituting into (L1) gives (L2).

For (L3): `||u_i psi - u_j psi|| <= ||u_i psi - psi|| + ||psi - u_j psi|| = sqrt(2delta_i) + sqrt(2delta_j)`.
Hence `|z_ij| >= Re<u_i psi, u_j psi> = 1 - ||u_i psi - u_j psi||^2/2 >= 1 - (sqrt delta_i + sqrt delta_j)^2`. QED.

*Sharpness.* For `k = 2`, `t = 1`, (L1) reads `delta_1 + delta_2 >= sin(pi/d)|z_12|`. The Harper
ground state has `delta_1 + delta_2 = pi/d + O(d^(-2))`. For the triangle `Z, X, e^(i pi/d)XZ` (all
`t_ij = +-1`), (L2) gives `sum delta >= sqrt3 sin(pi/d)(1 - O(1/d))`. The chirped Gaussian of
`qudit-weyl-rounding-constant-triangular-harper-bound-proof` has `sum delta = sqrt3 pi/d + O(d^(-2))`.
So neither inequality can be improved at leading order.

## Lemma T (four directions are never pairwise +-1 for d >= 5)

Let `d >= 5`. There are no four vectors `v_1, ..., v_4 in F_d^2` with `[v_a, v_b] in {1, -1}` for all
`a != b`.

*Proof.* Replace `v_2` by `-v_2` if needed so that `[v_1, v_2] = 1`. `Sp(2, F_d) = SL(2, F_d)` acts
transitively on such pairs, so we may take `v_1 = e_1` and `v_2 = e_2`. Write `v_3 = (a, b)`. Then
`[e_1, v_3] = b` and `[e_2, v_3] = -a`, so `a, b in {+-1}`. The same holds for `v_4 = (a', b')`. So
`[v_3, v_4] = ab' - ba' in {0, 2, -2}`. `2 = +-1 mod d` forces `d | 1` or `d | 3`, which is false for
`d >= 5`. QED.

## The rounding (line measurement)

For each line `l`, let `B_l` be the stabilizer basis of `l` (the joint eigenbasis of the `D(v)`,
`v in l`). Choose `l` with probability `lambda_l` and measure `psi` in `B_l`, obtaining a stabilizer
state `phi`. If `g_j` is on `l`, it is diagonal in `B_l`, so `E<phi|u_j|phi> = <psi|u_j|psi>`. If `g_j`
is not on `l`, then `<phi|u_j|phi> = 0`, because `phi` is an eigenvector of some `D(v)`, `v in l`, and
`u_j D(v) = omega^m D(v) u_j` with `m != 0`. Hence

```text
lambda_max - E<phi|K|phi> = sum_j |c_j| (1 - delta_j)(1 - lambda_(l(j))) .
```

This is at most `c F` if `(1 - delta_j)(1 - lambda_(l(j))) <= c delta_j` for every `j`. That holds
trivially when `delta_j >= 1`. When `delta_j < 1`, it holds iff
`lambda_(l(j)) >= 1 - c delta_j/(1 - delta_j)`. So the rounding certifies `c` whenever

```text
(R)   sum_l x_l <= 1,        x_l := max_(j : l(j) = l) ( 1 - c delta_j/(1 - delta_j) )_+   (x_l = 0 if no term is on l).
```

## Theorem

Let `d >= 5`, `s = sin(pi/d)`, `A = 2/(sqrt3 s)`, and let `c` satisfy `c > 3` and
`c (c-3)/(c+1) >= A`. Then (R) holds for every one-qudit `K`. Hence `c_d^(1) <= c*(d)`, the larger
root of `c^2 - (3+A)c - A = 0`.

*Proof.* Put `eta = (c-3)/(c+1) = 1 - 4/(1+c) > 0`. Then `c eta s >= 2/sqrt3`.

Suppose (R) fails. Let `S` be the set of lines with `x_l > 0`, and `k = |S|`. Then `k >= 2`, because
each `x_l <= 1`. For `l in S`, choose a term `j_l` on `l` attaining `x_l`, and write `delta_l`,
`u_l` for its data. `x_l > 0` means `delta_l < 1/(1+c)`. Failure of (R) gives
`k - 1 < c sum_S delta_l/(1 - delta_l)`. Since `1 - delta_l > 0`, this gives

```text
(1)   sum_(l in S) delta_l  <  (k - 1)/c .
```

The `u_l` lie on distinct lines, so every `t_ll' != 0`. By (L3), `|z_ll'| >= 1 - 4/(1+c) = eta`. By
(L2) with `w = 1`,

```text
(2)   sum_S delta_l  >=  eta ( sum_(l<l') sin^2(pi t_ll'/d) )^(1/2) .
```

Call a pair *short* if `t_ll' = +-1`, and let `E_1` be the number of short pairs. A non-short pair has
`t in {2, ..., d-2}` up to sign, so `sin^2(pi t/d) >= sin^2(2pi/d) = kappa s^2`, where
`kappa = 4cos^2(pi/d)`. For `d >= 5`, `kappa >= 4cos^2(pi/5) = 2.618`. So
`sum sin^2 >= s^2 (E_1 + kappa (binom(k,2) - E_1))`.

- `k = 2`: `sum sin^2 >= s^2`. Then (2) gives `sum delta >= eta s >= 2/(sqrt3 c) > 1/c`, which
  contradicts (1).
- `k = 3`: `sum sin^2 >= 3s^2`. Then (2) gives `sum delta >= sqrt3 eta s >= 2/c`, which contradicts (1).
  This is the tight case.
- `k >= 4`: by Lemma T the short-pair graph on `S` is `K_4`-free. By Turán's theorem `E_1 <= k^2/3`.
  So `sum sin^2 >= s^2 Q(k)`, where
  `Q(k) = kappa k(k-1)/2 - (kappa - 1) k^2/3 = k( (kappa+2)k/6 - kappa/2 )`. We claim
  `Q(k) >= (3/4)(k-1)^2`. The difference `Q(k) - (3/4)(k-1)^2` is linear in `kappa`, with coefficient
  `k(k-3)/6 > 0`. So it suffices to take `kappa = 2.618`. There it equals
  `0.01967 k^2 + 0.191 k - 0.75`, which is positive at `k = 4` (`0.329`) and increasing for `k >= 4`.
  Then (2) gives `sum delta >= eta s (sqrt3/2)(k-1) >= (k-1)/c`, which contradicts (1).

So (R) holds. Some outcome of the rounding attains at least the mean, so some stabilizer state has
`<phi|K|phi> >= lambda_max - cF`. QED.

## The constant

`c*(d) = ((3+A) + sqrt((3+A)^2 + 4A))/2 <= ((3+A) + (A+5))/2 = A + 4`, since
`(A+5)^2 = (3+A)^2 + 4A + 16`. Next, `sin x >= x(1 - x^2/6)` and `1/(1 - y) <= 1 + 2y` for
`y <= 1/2` give `A <= (2d/(sqrt3 pi))(1 + pi^2/(3d^2)) = 2d/(sqrt3 pi) + 2pi/(3 sqrt3 d)`. So

```text
c_d^(1) <= 2d/(sqrt3 pi) + 4 + 1.21/d .
```

The lower bound `c_d^(1) >= 2d/(sqrt3 pi) - 1 - O(d^2 e^(-d))` is the one-qudit instance of
`qudit-weyl-rounding-constant-triangular-harper-bound`. Together they give
`c_d^(1) = 2d/(sqrt3 pi) + O(1)`.

## Where the 4 comes from, and what is not claimed

- The additive gap between the bounds (`-1` against `+4`) comes from (L3): `eta = 1 - 4/(1+c)`
  costs `+4`. The numerics suggest that the true one-qudit constant is below the triangle lower
  bound plus `1`. For the line-measurement rounding used here, the local-search worst states give
  `sup_psi c_meas(psi) >= 1.531` (`d = 5`) and `>= 2.254` (`d = 7`) (`cmeas.py`). Sharpening (L3)
  with the phase of `z_ij` would lower the `+4`. This is not needed for the asymptotic constant.
- One qudit only. For `n >= 2` qudits the noncommutation graph is arbitrary, and Lemma T and the
  line structure are lost. The reduction of the `n`-qudit bound to a matrix inequality is
  `qudit-weyl-rounding-constant-2d-over-sqrt3-pi-via-trace-norm`.
- `d = 3`: Lemma T fails, because `2 = -1 mod 3`. `d = 2` is the qubit case, with the sharp value
  `1/sqrt2`.

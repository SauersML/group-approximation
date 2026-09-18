---
rg: 2
id: gaussian-pair-sum-chaos-eigenvalues-halve-every-two-degrees
kind: claim
title: For M_D = E_P Pi_P^(tensor D) on the centred tensor power (1^perp)^(tensor D) of R^(2n), where Pi_P = (I + sigma_P)/2 and sigma_P is a uniform perfect-matching involution, lambda_D = ||M_D|| is nonincreasing in D and at most 2^-ceil(D/2) + O_D(n^-1/2)
distinct_from:
  pair-resampling-walk-balanced-partitions-are-unstable: that is the Haar-frame (d = 2n) walk, whose T_P averages a rotation of the pair differences and does not factor through tensor powers of a label-space projection; this is the label-space operator that governs the Gaussian model, where T_P is exactly a second quantisation.
  affine-ug-easy-on-globally-hypercontractive-graphs: that is an algorithm on hypercontractive graphs; this is a spectral bound for one averaged tensor-power operator.
artifacts:
  - experiments/gaussian-rich-2to1-universe-2026-09-17/check_gaussian_universe.py
---

**ESTABLISHED.** Proof: route `gaussian-pair-sum-chaos-eigenvalue-pattern-count-proof`.

**Setting.** Fix `n >= 2`. Put `m = 2n`. For a perfect matching `sigma` of
`[m]`, viewed as a fixed-point-free involution and as a permutation matrix, put
`Pi_sigma = (I + sigma)/2`. This is the orthogonal projection of `R^m` onto
`span{e_a + e_sigma(a)}`. Let `sigma` be uniform over the `(m-1)!!` matchings.
`Pi_sigma` fixes `1` and preserves `1^perp`. Let

`M_D = E_sigma Pi_sigma^(tensor D)` restricted to `V_D = (1^perp)^(tensor D)`,

and `lambda_D = ||M_D||`. `M_D` is positive semidefinite, and `lambda_0 = 1`.

**Theorem.**

1. (Monotone.) `lambda_k <= lambda_j` whenever `k >= j`.
2. (Degree one.) `lambda_1 = (n-1)/(2n-1)`.
3. (Main bound.) For `D >= 1`, `2n > 2D` and `0 < eps <= 1`,

   `lambda_D <= (1+eps) 2^-ceil(D/2) + (1 + 1/eps) (D+1)^D (1 - D/(2n))^-D / (2n) + (Bell(D) D + 4 D^2)/(2n - D)`.

   With `eps = n^(-1/2)`: `lambda_D <= 2^-ceil(D/2) + C_D n^(-1/2)` for a
   constant `C_D` depending only on `D`.

**Computation.** The artifact computes `lambda_k` exactly by summing over all
matchings (seed irrelevant). Every row agrees with item 2 at `k = 1`, and the
limit `2^-ceil(k/2)` is visible from `n = 3`:

| `n` | `lambda_1` | `lambda_2` | `lambda_3` | `lambda_4` |
|---|---|---|---|---|
| 2 | 0.33333 | 0.33333 | 0.33333 | 0.33333 |
| 3 | 0.40000 | 0.40000 | 0.25000 | 0.25000 |
| 4 | 0.42857 | 0.42857 | 0.24660 | - |
| 5 | 0.44444 | 0.44444 | 0.24681 | - |

The pairs `lambda_(2j-1) ~ lambda_(2j)` match the main term. It counts the
ways to split a tuple of `D` labels into pairs of equal labels: a tuple with
`q_2` repeated values is fixed, in the limit, by `2^(q_2)` of the `2^D`
choices of which coordinates the involution acts on, and `q_2 <= D/2`.

**Why it matters.** In the Gaussian pair-sum universe, the pair-resampling walk
acts on the degree-`D` Wiener chaos of the centred part as a restriction of
`I tensor M_D` (`gaussian-universe-rich-2to1-game-has-vanishing-value`). So
this bound is the high-degree half of a hypercontractive stability bound. The
low-degree half is Gaussian hypercontractivity.

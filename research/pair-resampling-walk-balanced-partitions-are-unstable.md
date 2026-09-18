---
rg: 2
id: pair-resampling-walk-balanced-partitions-are-unstable
kind: claim
title: Every S_2n-equivariant, frame-sum-balanced fractional partition of orthonormal 2n-frames has pair-resampling stability o(1) as n grows
distinct_from:
  rotated-frame-value-reduces-to-partition-stability: that proves val^4 <= 4 Stab_T(rho_A) for the rotated-frame universe game; this is the analytic premise that the stability tends to 0, which is not proved.
  affine-ug-easy-on-globally-hypercontractive-graphs: that is an algorithm for affine unique games on noisy Johnson, Grassmann and HDX walks; this is a small-partition stability bound for a different walk (resampling pair differences of a frame), wanted for soundness rather than algorithms.
  walsh-frame-rich-2to1-games-have-value-near-one: that is a high-value theorem for Walsh frames; this is a conjectured low-stability bound for Haar frames.
artifacts:
  - experiments/pair-resampling-hypercontractivity-2026-09-17/chaos_eigen.py
  - experiments/pair-resampling-hypercontractivity-2026-09-17/orthogonal_harmonic_eigen.py
  - experiments/pair-resampling-hypercontractivity-2026-09-17/linear_partition_stability.py
---

**OPEN.**

**Statement.** Let `d_n >= 2n`, and let `mu` be the Haar measure on orthonormal
`2n`-tuples `X = (x_a)` in `R^(d_n)`. Put:

* `s = sum_a x_a`;
* `T_P = E[. | Pi_P X]` for a labelled 2-to-1 map `P`, where
  `(Pi_P X)_b = sum_(a in P^(-1)(b)) x_a`;
* `T = E_P T_P`, the pair-resampling walk.

A *balanced equivariant partition* is `rho = (rho_a)_(a in [2n])` with:

* `rho_a >= 0` and `sum_a rho_a = 1`;
* `rho_a(sigma X) = rho_(sigma^(-1)(a))(X)` for all `sigma in S_2n`;
* `E[rho_a | s] = 1/(2n)`.

The claim is

`sup_rho Stab_T(rho) = sup_rho sum_a <rho_a, T rho_a>  ->  0   (n -> infinity)`.

By `rotated-frame-value-reduces-to-partition-stability`,
item 4, this gives `val(U_(n,d_n)) -> 0` for the rotated-frame universe rich
2-to-1 game. That game is a continuum perfect basic-SDP gap for BKM
Conjecture 7 (`rich-2to1-perfect-completeness-conjecture`). Any `d_n` works.
The case `d_n = 2n` is the orthogonal group, and `d_n -> infinity` is the
Gaussian model below.

**Prerequisites a proof needs, each of which can fail.**

* **(H1) Low-degree contraction on the fibres of `s`.** `T` must contract
  every Hermite/harmonic degree `k >= 1`, orthogonal to functions of `s`, by a
  factor `c^k` with `c < 1`, up to an additive `epsilon_n -> 0`.
* **(H2) A hypercontractive inequality for `T` restricted to those fibres.**
  Only the level-`k` contraction is known here, so (H2) is where a
  global-hypercontractivity argument, in the style of the multi-slice and
  Johnson-scheme results, is needed. On high degrees the floor `epsilon_n` must
  stay `o(1)`.
* **(H3) Balance kills the invariant part.** This is proved (item 3 of the
  lemma), so it is not a risk.

## Attempts

* **Uniform Ornstein--Uhlenbeck domination fails at high degree (2026-09-17,
  obstruction).** One would like `T <= Gamma(c)` on the fibres of `s` for a
  fixed `c < 1`, followed by Nelson's inequality.
  - Take the Gaussian model (`d -> infinity`). There `T` is the second
    quantisation `E_P Gamma(Pi_P)`, acting on degree-`k` chaos by
    `E_P Pi_P^(tensor k)` on `(1^perp)^(tensor k)`.
  - Take `v = e_1 + e_2 - e_3 - e_4` in `1^perp`. Whenever `P` pairs `{1,2}`
    and `{3,4}`, `Pi_P v = v`. So
    `<v^(tensor k), T v^(tensor k)> / |v|^(2k) >= Pr[P contains {1,2},{3,4}] = 1/((2n-1)(2n-3))`
    for every `k`.
  - Hence `lambda_k >= 1/(4n^2)` for all `k`, and `T <= Gamma(c)` fails once
    `c^k < 1/(4n^2)`, that is for `k > 2 log_2(2n) / log_2(1/c)`.
  - Invariant: the probability that one sparse pairing pattern survives.
  - Step where it dies: degree `k ~ log n`.
  - Survivor: the additive form `lambda_k <= c^k + epsilon_n`, which the
    obstruction allows with `epsilon_n = O(n^(-2))`.
* **Conditional implication, Gaussian model (2026-09-17, proved there).**
  Suppose `lambda_k <= c^k + epsilon` for all `k >= 1`, where `lambda_k` is the
  top eigenvalue of `E_P Pi_P^(tensor k)` on `(1^perp)^(tensor k)`.
  - Split the Gaussian matrix as `s` plus the independent `1^perp` part. `T`
    acts as the identity on `s` and preserves chaos degree in the `1^perp` part.
    So `T <= Id_s tensor (Gamma(c) + epsilon)`.
  - Nelson gives `<f, Gamma(c) f> <= ||f||_(1+c)^2`. Since
    `0 <= rho_a <= 1` and `E[rho_a | s] = 1/(2n)`, this yields
    `Stab_T(rho) <= sum_a E_s (E[rho_a^(1+c) | s])^(2/(1+c)) + epsilon <= (2n)^(-(1-c)/(1+c)) + epsilon`.
  - With `c = 1/sqrt 2` the exponent is `(sqrt 2 - 1)^2 = 0.1716`. Any `c < 1`
    gives vanishing stability.
  - For comparison, the linear partition `argmax_a <x_a, w>` sees coordinate
    correlation `1/2` under one resampling step. Borell's bound then predicts
    stability `(2n)^(-1/3)`, the exponent of `c = 1/2`. The value of the linear
    strategy pair sees correlation `1/sqrt 2` between `x_a` and `y_b / sqrt 2`,
    and has predicted exponent `(sqrt 2 - 1)^2`.
  - So the premise follows in the Gaussian model from
    `lambda_k <= 2^(-k/2) + O(n^(-2))`. That bound is **not proved**.
* **Numerics for `lambda_k` (Gaussian model).** Source:
  `experiments/pair-resampling-hypercontractivity-2026-09-17/chaos_eigen.py`,
  exact enumeration of pairings, top eigenvalues by Lanczos.

  | `n` | `lambda_1` | `lambda_2` | `lambda_3` | `lambda_4` |
  |---|---|---|---|---|
  | 2 | 1/3 | 1/3 | 1/3 | 1/3 |
  | 3 | 0.4 | 0.4 | 0.25 | 0.25 |
  | 4 | 0.4286 | 0.4286 | 0.2466 | — |
  | 5 | 0.4444 | 0.4444 | 0.2468 | 0.2468 |
  | 6 | 0.4545 | 0.4545 | 0.2473 | — |

  - `lambda_1 = (n-1)/(2n-1)` exactly, because `E_P Pi_P = (I + (J - I)/(2n-1))/2`.
    The tensor `I_(1^perp)` (the function `|x_tilde|^2`) has Rayleigh quotient
    `tr(Pi_P C)/(2n-1) = (n-1)/(2n-1)`, so `lambda_2 >= (n-1)/(2n-1)`.
    Equality holds numerically.
  - The pattern suggests `lambda_k ~ 2^(-ceil(k/2))`. That is at most
    `2^(-k/2)`, with near-equality at even `k`, so `c = 1/sqrt 2` looks
    critical.
  - The high-degree floor `1/((2n-1)(2n-3))` is below every value computed.
  - Evidence only.
* **Orthogonal group `d = 2n` (murky).** Source: `orthogonal_harmonic_eigen.py`.
  - It builds `E_P Proj(O(V_P^perp)-invariants)` on `(R^(2n))^(tensor k)` for
    `k <= 3` and removes the `Stab(1)` Brauer invariants.
  - Top eigenvalue overall: `(n-1)/(2n-1)`. Top on the `1^perp`-chaos at
    `k = 2`: `0.2778` (n=3), `0.25` (n=4), `0.2429` (n=5). The `k = 3` value
    `0.4286` at `n = 4` comes from tensor redundancy: `v tensor I` contracts to
    degree 1, so the tensor space overcounts harmonics.
  - These are not eigenvalues of `T` on `L^2(O(2n))` harmonics.
* **Monte Carlo on the linear equivariant partition, `d = 2n`.** Source:
  `linear_partition_stability.py`.
  - `Stab_T = 0.30066, 0.17242, 0.09915, 0.05798, 0.03430` at
    `n = 4, 16, 64, 256, 1024`, a fitted slope of about `n^(-0.38)` over this
    range.
  - This is consistent with the claim, and shows that the natural
    candidate strategy is not a counterexample.
* **Spectral-gap / Holder route: too lossy.** A degree-1 gap `lambda_1 < 1/2`
  plus trivial bounds on higher degrees gives only `Stab_T <= 1/2 + O(1/n)`.
  Heuristically, `2n`-part balanced partitions carry most of their mass at
  degree `~ log n`, so a hypercontractive inequality (H2) is needed.
  - The Gaussian-model constant is `sup_k lambda_k = (n-1)/(2n-1)`, assuming
    equality at `k = 2`.
* **Candidate transplant, not attempted.** The global hypercontractivity of the
  multi-slice (Braverman--Khot--Lifshitz--Minzer, arXiv:2110.10725) and of
  `S_n` (Filmus--Kindler--Lifshitz--Minzer). The obstruction above is a *global*
  function concentrated on a pairing pattern, which is exactly what those
  theorems handle, with the global/non-global dichotomy.
  - A route would show: equivariance plus balance forces `rho_a` to be global,
    in the sense that restrictions to pairing patterns do not raise `L^2` mass;
    otherwise a restriction gives a contradiction with `E[rho_a | s] = 1/(2n)`
    and symmetry.

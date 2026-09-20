---
rg: 2
id: dkkms-quotient-covering-proves-99-percent-rigidity
kind: claim
title: The DKKMS seed law is close to uniform after quotienting by H_U, at chi-square exp(k beta^2 2^(l-1)) - 1 instead of the X_U-level 4^l scale, so Theorem R holds with the quotient covering error SD^cl in place of SD*, and local 99 percent rigidity holds at every admissible parameter point with l >= 66
distinct_from:
  dkkms-near-perfect-labellings-are-outer-honest: that proves Theorem R with the X_U-level covering error SD* = beta sqrt(k) 2^(l+3) + 3 * 2^(l-k), which needs k of order 4^l; this runs the rigidity lemma on the class table over Gr(X_U/H_U, l) and needs only the quotient error SD^cl, of order beta sqrt(k) 2^((l-1)/2), which is small from k of order 2^l polylog(l) on.
  dkkms-seed-law-is-uniform-in-regime-and-far-in-window: that proves the X_U-level seed law is at total variation >= 3/4 - 1/ln k from every transitive law on the q = 1 window and kills transfers from a transitive test on Gr(X_U, l-1); this transfers from the transitive test on Gr(X_U/H_U, l-1), outside that class, and the image of the seed law there is within 10^(-5) of uniform on the whole window once l >= 66.
  near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp: that proves Theorem S in the regime SD* <= 10^(-5); this extends its hypothesis to SD^cl <= 10^(-5), which is every admissible point with l >= 66.
  dkkms-certified-parameters-lie-in-the-selector-kill-regime: that places the DKKMS-certified points inside the SD* regime; this covers the uncertified admissible points as well.
  dkkms-grassmann-2to1-test-is-locally-99-percent-rigid: that is the rigidity target with an unnamed l_0; Corollary T here proves it with eta_1 = 10^(-5), zeta_1 = 1/128 and l_0 = 66.
artifacts:
  - experiments/dkkms-class-covering-2026-09-17/check_class_covering.py
---

**ESTABLISHED.** Route: `dkkms-quotient-covering-proves-99-percent-rigidity-proof`.

## Setting

The notation is that of `dkkms-near-perfect-labellings-are-outer-honest`.

* `U` is a k-tuple of variable-disjoint equations, `X_U = F_2^(3k)` in `k`
  blocks of 3 coordinates, and `H_U` is spanned by the block all-ones vectors.
* `Y := X_U / H_U = Y_1 + ... + Y_k` with `Y_i = F_2^3/<111>`, so `dim Y = 2k`.
  Write `pi : X_U -> Y` for the quotient map.
* `V` keeps equation `i` with probability `1 - beta`. Otherwise it keeps one
  variable `v` of block `i`, drawn from a law `nu_i` (uniform in DKKMS). Put
  `s_i := sum_v nu_i(v)^2 <= 1`.
* The seed is `L'`, uniform in `Gr(X_V, l-1)`. Its image is
  `Qbar := pi(L')`.

Define the quotient covering error

```text
chi*  := (1 - 2^(l-1-k))^(-2) * exp(k beta^2 (2^(l-1) - 1)) - 1,
SD^cl := (1/2) sqrt(chi*) + 3 * 2^(l-k).
```

For small `x = k beta^2 2^(l-1)`, `SD^cl` is about
`beta sqrt(k) 2^((l-1)/2)`. That is `2^((l+7)/2)` times smaller than
`SD* = beta sqrt(k) 2^(l+3) + 3 * 2^(l-k)`.

## Statements

**Theorem CL (quotient covering).** Let `d = l - 1 < k`, fix `U`, and let `mu_U`
be the law of `Qbar` given `U` and `L' meet H_U = 0`. Then

```text
chi^2(mu_U || unif Gr(Y, d))  <=  (1 - 2^(d-k))^(-2) prod_i (1 + beta^2 s_i (2^d - 1)) - 1  <=  chi*.
```

Also, given `V` and `L' meet H_U = 0`, `Qbar` is exactly uniform on
`Gr(W_V, d)`. Here `W_V = pi(X_V)` is the sum of `Y_i` over kept blocks and
of `<pi(e_v)>` over smoothed blocks.

**Theorem R^cl.** Let `l >= 3`, `2^(l-k) <= 1/200` and `2k >= 3`. The four
conclusions of Theorem R of `dkkms-near-perfect-labellings-are-outer-honest`,
and those of its Corollary P, hold with `SD*` replaced by `SD^cl`. The
hypothesis `2^(l-1) beta <= 1/8` is not needed. Item 1 improves: `lambda_U`
satisfies every equation of `U`, for every `U`.

**Corollary N^cl.** If `eta <= 10^(-5)` and `SD^cl <= 10^(-5)`, then there is
an outer labelling `lambda` with

* `val_(Phi_k)(lambda) >= 0.994 >= 15/16`;
* dirt `<= 0.0032 <= 1/64`;
* disagreement with `hon_kappa(lambda)` `<= 0.0074 <= 1/128`.

**Corollary T.** `dkkms-grassmann-2to1-test-is-locally-99-percent-rigid` holds
with `eta_1 = 10^(-5)`, `zeta_1 = 1/128` and `l_0 = 66`. For every `l >= 66`,
every advice dimension `q >= 1` and every `k` admissible for Corollary A
(`2^(l-1-2k) <= 1/16` and `eps_k = exp(-k/e^(ql)) <= p0^2/4`), one has
`SD^cl(l, k) <= 10^(-5)`. This holds in the natural and base-2 readings of
`beta = log log k / k` and for every smoothing law `nu_i`.

**Corollary S^cl.** Theorem S of
`near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp` holds at every
point satisfying (A) and `l >= 3`, `SD^cl <= 10^(-5)`. In particular it holds
at every admissible point with `l >= 66` and `q >= 1`. So is Corollary B of
`high-advantage-selector-witnesses-decode-good-outer-labellings`, now with its
rigidity hypothesis discharged. A randomized polynomial-time branch selector
whose YES lifts reach value `1 - 10^(-5)` puts the source problem in RP.

## What it does

* **Closes the last hole of the rigidity target (type 1).** The target was
  equivalent to `T2`, its restriction to admissible points outside (R). `T2`
  is proved for `l >= 66`, and the target's `l_0` is `66`. At `q = 1` and
  `l = 90`, for example, `SD*(k_A) = 1.1e8` while `SD^cl(k_A) = 1.4e-7`. The
  first point with `SD* <= 10^(-5)` has `ln k >= 155.2`, against
  `ln k_A = 94.9`.
* **Changes what was believed (type 4).** By Corollary T of
  `dkkms-seed-law-is-uniform-in-regime-and-far-in-window`, "no covering or
  coupling transfer from a uniform Grassmann test proves T2". That is true
  only for tests on `Gr(X_U, .)`, which is the class that node kills. Every
  event of the per-tuple argument is `H_U`-invariant: the rejection of two
  extensions and the disagreement with `lambda_U`. So the transfer can be
  done from the uniform test on `Gr(X_U/H_U, .)`. There the seed law
  collides at rate `2^(l-1)` per doubly smoothed block instead of `4^(l-1)`.
  - The dead density-comparison lease on this node has exponent
    `k beta^2 4^(l-1)/3`, and it is right about the `X_U` level.
  - The quotient exponent is `k beta^2 2^(l-1) s`. It goes to `0` on the whole
    window, because `k_A ~ e^l` exceeds `2^l`.
  - The wave-19 class-seed band `t = beta sqrt(k) 2^(l/2)/sqrt(l) <= 2` is not
    untouched. Rigidity and Theorem S reach every point with
    `t sqrt(l)/2 <~ 10^(-5)`.
* **Selector route.** Under `NP not in RP`, the near-perfect form of
  `efficient-branch-selector-on-proved-2to1-instances` is false at every
  admissible DKKMS point with `l >= 66`. Constant-bias selectors with
  completeness below `1 - 10^(-5)` are untouched.

This neither proves nor refutes UGC.

## Not covered

* `3 <= l <= 65` at the admissible points with `SD^cl > 10^(-5)`. At `q = 1`
  these are the points with `k_A(l) <= k` and `k` below the `SD^cl`
  threshold.
* A real advice constant `q` in `(0, ln 2]`. There `k_A ~ e^(ql)` does not
  beat `2^l`. For real `q > ln 2` the same proof gives an `l_0(q)`: the
  artifact finds `l_0(0.8) = 175`, `l_0(0.75) = 321` and `l_0(0.72) = 662`.
* Completeness away from `1` and the KMS 2-to-2 instances.

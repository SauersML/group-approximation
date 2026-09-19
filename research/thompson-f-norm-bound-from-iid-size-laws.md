---
rg: 2
id: thompson-f-norm-bound-from-iid-size-laws
kind: claim
title: "Simple random walk on Thompson's group F has Markov operator norm above 0.9698 (two explicit tree-size laws), above the HHR estimate 3.87/4 and the EP-G extrapolation mu ~ 15.0"
distinct_from:
  thompson-f-norm-bound-from-forest-renewal-test-vector: that certifies ||P|| > 0.9397 with 6320 optimised split weights at cutoff N = 80 and a finite window n = 30000; this certifies ||P|| > 0.9698 from two size laws with 24 log-scale knots each at cutoff N = 10^6, through the exact n -> infinity limit, and it crosses the HHR and EP-G estimates that one left standing.
  thompson-f-norm-bound-from-epg-32-term-moments: that certifies ||P|| > 0.910677 from 32 cogrowth terms; this uses no moment data.
  thompson-f-norm-bound-from-hhr-exact-moments: that certifies ||P|| > 0.901532 from 25 moments.
  thompson-f-random-walk-norm-certified-lower-bound: that certifies ||P|| > 0.880541 from counts to length 30.
  thompson-f-iid-forest-vectors-cannot-reach-norm-one: that caps this whole test-vector family at 79/80, so this route cannot prove amenability; this is the lower-bound use of the same reduction.
artifacts:
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/certify_iid.py
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/certify_N1000000.out
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/certify_N640.out
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/spline_opt.py
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/spline_K24_N1000000.npy
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/spline_K24.out
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/size_law_problem.py
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/crosscheck_w13.py
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/crosscheck_w13.out
---

**ESTABLISHED (computer-assisted, exact integer arithmetic).** Let
`P = (x_0 + x_0^{-1} + x_1 + x_1^{-1})/4` act on `l^2(F)`. Then

    ||P|| >= J_lo/4 = 0.96987657...  >  4849/5000 = 0.9698.

**Consequences.**
- *Cogrowth rate.* `mu = 16 ||P||^2 > 15.0481`.
- *Norm of the generator sum.* `||x_0 + x_0^{-1} + x_1 + x_1^{-1}|| > 3.8792`.
- *Reduced cogrowth.* Grigorchuk's formula `4||P|| = alpha + 3/alpha` gives `alpha > 2.8125`. The
  amenable value is `3`.
- *Gap to amenability.* `1 - ||P|| < 0.0302`, down from `0.0603`.

**Belief change: two more published numerical estimates are wrong.** Quoted verbatim in
`research/artifacts/thompson-f-cogrowth-literature-pins-2026-09-13.md` and
`thompson-f-norm-bound-from-epg-32-term-moments`:
- *Haagerup–Haagerup–Ramirez-Solano.* Their computations "suggest ... `||A+A^{-1}+B+B^{-1}|| ≈ 3.87`".
  The certified norm exceeds `3.879`.
- *Elvey Price–Guttmann.* They extrapolate `mu ≈ 15.0`, that is `||P|| ≈ 0.9682`. The certified
  `mu` exceeds `15.048`.
- *ERJvR.* Their `2.53±0.03` was already refuted by `thompson-f-norm-bound-from-forest-renewal-test-vector`.
  The certified reduced cogrowth `2.8125` now sits about ten of their standard errors above it.

Every published numerical estimate of this norm known to the graph now lies below a certified lower
bound. The numerical evidence for non-amenability has repeatedly underestimated the norm. The
sequence of certified floors is `0.8805 -> 0.9015 -> 0.9107 -> 0.9397 -> 0.9698`.

**Method.**
- *Reduction.* By `thompson-f-iid-forest-vectors-cannot-reach-norm-one` (step 4 of its route),
  the pointed-forest product vectors with split shapes realise, as `n -> ∞`, exactly

      J(alpha, beta) = 2 BC(alpha, beta)^2 + 2 sum_{j<=N} sqrt(beta_j (alpha*beta)_j)

  for any size laws `alpha, beta` with `alpha_1 > 0`. So `||x_0+x_0^{-1}+x_1+x_1^{-1}|| >= J`. This
  needs no finite-window evaluation at all.
- *The instance.*
  - `N = 10^6`. The laws have `log alpha_k` and `log beta_k` piecewise linear in `ln k` with 24 knots
    each (`spline_K24_N1000000.npy`), minus `(1/2) ln k`.
  - They are frozen as nonnegative integers `floor(2^40 alpha_k)`, `floor(2^40 beta_k)`. The
    sha256 of the integer arrays is recorded in `certify_N1000000.out`.
- *Exact evaluation* (`certify_iid.py`).
  - `alpha * beta` is computed exactly by NTTs modulo four primes and CRT. The script asserts that
    the CRT modulus exceeds the size bound. It checks the identity `c(x) = alpha(x) beta(x)` exactly at
    `x = ±1` and at three random points modulo `2^61 - 1`, and cross-checks against a float FFT.
  - The square roots are bounded below by `isqrt` at scale `2^64`, and `sqrt(sum alpha)` above.
  - The resulting `J_lo` is a Fraction with `J_lo <= J`, and `J_lo/4 > 4849/5000` is checked exactly.
  - The run takes a few minutes in pure Python/numpy.

**Provenance does not matter.** Any nonnegative integer laws with `alpha_1 > 0` give a valid bound.
The float construction only proposes them. On another platform, `exp`/`log` rounding may change a
few integers, and the printed `J_lo` then moves in the 12th digit.

**Scope.**
- Lower bound only. It says nothing about amenability.
- The ceiling theorem caps this family at `0.9875`, and heuristically at `0.9744` (continuum limit), so
  the method cannot go much further.
- Larger `N` gains about `0.0018` per decade: `0.96494, 0.96809, 0.96988` at `N = 10^4, 10^5, 10^6`.

Proof route: `thompson-f-norm-bound-from-iid-size-laws-proof`.

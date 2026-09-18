---
rg: 2
id: fpbs-tree-connection-zeros-linear-past-flat-edge
kind: claim
title: On the regular tree the walk rate is flat exactly up to p_lambda=(d-1)^(-1/2), so the connection polynomials have linearly many zeros in every symmetric domain whose real trace passes p_lambda, including the disc |z-1/2|<1/4 on T_3
distinct_from:
  fpbs-connectivity-polynomials-zero-free-around-criticality: that is the universal zero-free hypothesis ZG, supported on T_3 by a zero-free scan of |z-1/2|<1/4 for n<=200; this proves that on T_d ZG can hold only on domains whose real trace stays below p_lambda, that the scanned disc carries linearly many zeros, and exhibits a zero of a_2000 inside it
  fpbs-sublinear-zero-interpolant-iff-flat-rate: that is the general equivalence on Cayley graphs; this computes the tree rate exactly and applies it
artifacts:
  - research/artifacts/fpbs-sublinear-zero-flat-rate-2026-09-18.md
  - experiments/fpbs-zero-count-flat-rate-2026-09-17/tree_zero_count_linear.py
  - experiments/fpbs-zero-count-flat-rate-2026-09-17/exact_zero_check.py
---

**ESTABLISHED.** Proof in `fpbs-tree-connection-zeros-linear-past-flat-edge-proof`.

**Setting.** `T_d` is the `d`-regular tree, `d>=3`, the Cayley graph of
`Z/2 * ... * Z/2` (`d` factors). `X_n` is simple random walk from `o`,
`rho = 2(d-1)^(1/2)/d`, `p_c = 1/(d-1)`, `p_lambda = (d-1)^(-1/2)`, and
`phi(z) = ((d-1) z + 1/z)/d`. Since `o <-> x` iff the geodesic is open,

    a_n(z) = sum_k P(|X_n| = k) z^k,

and `a_(n,R) = a_n` for every `R >= n`.

**Theorem.**

1. *(Exact rate.)* `lambda(p) = rho` for `0 < p <= p_lambda`, and
   `lambda(p) = phi(p) > rho` for `p_lambda < p < 1`. More precisely
   `a_n(p) <= rho^n` for `p <= p_lambda`, and for `p > p_lambda`
   `a_n(p) = C(p) phi(p)^n + O(rho^n)` with
   `C(p) = (p - w) G(1/phi(p))/phi(p) > 0`, `w = 1/((d-1)p)`,
   `G(s) = sum_t P(X_t = o) s^t`.
2. *(Linear zeros.)* Let `U` be a simply connected domain with
   `conj(U) = U` that contains a point of `(0,p_lambda)` and a point
   `p_+` of `(p_lambda,1)`. Then there are a compact `K` in `U` and `c > 0`
   such that `a_n` has at least `c n` zeros in `K` for all large `n`.
3. *(ZG on trees.)* Hypothesis (ZG) of
   `fpbs-connectivity-polynomials-zero-free-around-criticality`, with
   exact zero-freeness, can hold on `T_d` only if `I_+` lies in
   `(p_c, p_lambda]`. With `o(n)` zeros on compacts and symmetric `U`, it can
   hold only if `U` contains no point of `(p_lambda, 1)`.
4. *(The scanned disc.)* On `T_3` (`p_lambda = 0.70711`), the disc
   `|z - 1/2| < 1/4` contains `(0.3, 0.7)` and `0.74`, so by 2 some compact
   subset of it carries linearly many zeros of `a_n`. The 2026-09-17 scan found
   no zero for `n <= 200`; that is a finite-size effect. `a_2000` has the
   conjugate pair of zeros `0.7325276 +- 0.0588817 i`, with
   `|z - 1/2| = 0.23987`, confirmed by exact integer arithmetic
   (`exact_zero_check.py`).

**Numerics (not part of the proof).** The zeros accumulate on
`Gamma = {|phi| = rho, |z| >= p_lambda}`, which leaves `p_lambda` at +-45
degrees. The predicted count in a disc is `n alpha_max/pi`, where `alpha_max` is
the largest `arg phi` on `Gamma` inside it. For `|z - 1/2| < 1/4` that is
`0.00099 n`, which is about `0.2` at `n = 200` and `7.9` at `n = 8000`. The
observed counts at `n` = 200, 1000, 2000, 4000 and 8000 are 0, 0, 2, 4 and 8.
Tables are in the artifact.

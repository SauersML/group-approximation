---
rg: 2
id: all-ranks-occur-iff-continuous-ranks-are-dense-proof
kind: route
title: Greedy continuous residuals and Edwards increments prove the continuous-rank criterion for all ranks occurring
target: all-ranks-occur-iff-continuous-ranks-are-dense
requires: []
---

Standard inputs, used only in the forms stated.

- (Q) For unital separable `A`, `QT(A)` is a metrizable Choquet simplex
  (Blackadar--Handelman, J. Funct. Anal. 45 (1982), Section II.4).
- (E) Edwards's separation theorem on a Choquet simplex: a lower
  semicontinuous affine `f: QT(A) -> (-infinity, infinity]` is the pointwise
  supremum of an increasing sequence of continuous affine functions. This is
  the form already used in
  `research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md`, §3(iii).
- (D) For each `tau`, `d_tau: Cu(A) -> [0, infinity]` is additive, order
  preserving and preserves suprema of increasing sequences, and `d_tau(ta) =
  d_tau(a)` for `t > 0`. For fixed `a`, `tau -> d_tau(a)` is affine and lower
  semicontinuous. Rordam's lemma: `||a - b|| < eps` implies
  `(a - eps)_+ <~ b`.

**Orthogonal sums.** Let `a_k in (A tensor K)_+`. Identify
`A tensor K = A tensor K tensor K` and put
`a = sum_k 2^(-k) (1 + ||a_k||)^(-1) a_k tensor e_kk`. The series converges in
norm. The partial sums `a^(K)` satisfy `a^(K) <= a` and
`||a - a^(K)|| <= 2^(-K)`, so `[a] = sup_K [a^(K)]` by (D). Hence
`d_tau(a) = sum_k d_tau(a_k)` for every `tau`.

**(1) => (2) => (3).** Immediate: a rank equal to a continuous `f` is a
continuous rank at distance `0`.

**(3) => (2).** Let `f` be strictly positive continuous affine. Put `r_0 = f`.
Given a continuous affine `r_k > 0`, let `m_k = min r_k > 0` and
`M_k = max r_k`. The function `r_k - m_k/2` is continuous affine with minimum
`m_k/2 > 0`. Item 3 gives `a_(k+1)` with `d(a_(k+1))` continuous and
`|d(a_(k+1)) - (r_k - m_k/2)| < m_k/4`. Put `r_(k+1) = r_k - d(a_(k+1))`.
Then `r_(k+1)` is continuous and affine, and pointwise
`m_k/4 < r_(k+1) < 3 m_k/4`. By compactness `min r_(k+1) > 0`, and
`M_(k+1) < (3/4) m_k <= (3/4) M_k`. So `M_k <= (3/4)^k M_0 -> 0`, and
`sum_k d(a_k) = f` uniformly. The orthogonal sum of the `a_k` has rank `f`.

**(2) => (1).** Let `f: QT(A) -> (0, infinity]` be lower semicontinuous affine.
It attains its minimum `m > 0` on the compact `QT(A)`. By (E) choose continuous
affine `g_n` increasing pointwise to `f`. The open sets `{g_n > m/2}` increase
and cover `QT(A)`, so some `g_N > m/2` everywhere, hence `min g_N > m/2`. Put

```text
h_1     = g_N - m/4,
h_(k+1) = (g_(N+k) - g_(N+k-1)) + m (4^(-k) - 4^(-(k+1))).
```

Each `h_k` is continuous affine with `h_k >= (3/4) m 4^(-k) > 0` for `k >= 2`
and `min h_1 > m/4`. The partial sums are
`h_1 + ... + h_(k+1) = g_(N+k) - m 4^(-(k+1))`, which increase to `f`.
Item 2 realizes each `h_k` as `d(a_k)`. The orthogonal sum of the `a_k` has
rank `sum_k h_k = f`, including at points where `f = infinity`.

**Summands of a continuous rank.** If `d(a) + d(b)` is finite and continuous,
then `d(a)` is lower semicontinuous and equals a continuous function minus a
lower semicontinuous one, hence is also upper semicontinuous. For a countable
orthogonal sum, apply this to one summand against the orthogonal sum of the
rest, whose rank is lower semicontinuous by (D). Square.

---
rg: 2
id: barycentric-curvature-certificate-girth-bound-proof
kind: route
title: Summing the three link conditions around an incidence cycle gives the girth bound
target: barycentric-curvature-certificates-need-incidence-girth-eight
requires:
  - commuting-nonscalar-readouts-force-coset-four-cycles
---

Notation as in `barycentric-curvature-certificates-need-incidence-girth-eight`.
The cycle `c_1 - v_1 - ... - c_k - v_k - c_1` uses the `2k` incidences
`(c_i, v_(i-1))` and `(c_i, v_i)`, `i = 1..k`, each exactly once. Write
`t_i^- = (c_i, v_(i-1))` and `t_i^+ = (c_i, v_i)`.

## Three lower bounds

1. **At `J`.** The cycle is an injective cycle of `Inc(D)`, the link at `J`.
   Hence `sum_(i=1)^k (gamma(t_i^-) + gamma(t_i^+)) >= 2 pi`.
2. **At `H_(v_i)`.** The variable `v_i` lies in the distinct contexts `c_i` and
   `c_(i+1)`, and `|H_(v_i) : J| >= 2` gives a coset `hJ != J`. In the complete
   bipartite link at `H_(v_i)` the four vertices `c_i, J, c_(i+1), hJ` form an
   injective cycle of length `2 beta(t_i^+) + 2 beta(t_(i+1)^-)`. Hence
   `beta(t_i^+) + beta(t_(i+1)^-) >= pi`, and summing over `i` gives
   `sum (beta) >= k pi`.
3. **At `A_(c_i)`.** Put `H = H_(v_(i-1))` and `K = H_(v_i)`. A cycle of length
   `2 m_i` in the coset multigraph `Gamma(A_(c_i); H, K)` passes through `2 m_i`
   edges `gJ`. Each edge from `gH` to `gK` becomes the path `gH - gJ - gK` in
   the link at `A_(c_i)`, of length `alpha(t_i^-) + alpha(t_i^+)`. An injective
   cycle in the multigraph gives an injective cycle in the link, since distinct
   edges give distinct middle vertices `gJ`. Hence
   `2 m_i (alpha(t_i^-) + alpha(t_i^+)) >= 2 pi`, i.e.
   `alpha(t_i^-) + alpha(t_i^+) >= pi/m_i`. When `m_i = +infinity` this is
   vacuous.

## Summation

Each triangle has angle sum at most `pi`, and there are `2k` triangles, so

```text
2 pi + k pi + sum_i pi/m_i  <=  sum_t (alpha_t + beta_t + gamma_t)  <=  2 k pi,
```

which is (CB1).

## (CB2)

If every readout on the cycle is nonscalar, then consecutive readouts
`y_(v_(i-1)), y_(v_i)` commute (they share `c_i`). By (CN3) of
`commuting-nonscalar-readouts-force-coset-four-cycles`, `m_i = 2` when
`H cap K = J` and `m_i = 1` otherwise. With `r` values equal to `1`,
`sum_i 1/m_i = (k - r)/2 + r = (k + r)/2`, and (CB1) becomes
`2 + (k + r)/2 <= k`, i.e. `k >= 4 + r`.

The two forbidden patterns are the cases `k = 2` and `k = 3`. The certificate
hypothesis `|H_(v_i) : J| >= 2` holds because a nonscalar readout is not in
`C[J] p_omega = C p_omega`.

## (CB3)

In the subdivided cycle each inserted context `c'` contains a pair `(v, v')`
with `y_(v') in C*(1, y_v)`, so by (CN2) `H_v cap H_(v')` is strictly larger than
`J`, and `m = 1` at `c'`. So at least `s` of the `k + s` values are `1`, and
(CB2) gives `k + s >= 4 + s`.

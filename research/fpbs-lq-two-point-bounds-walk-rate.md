---
rg: 2
id: fpbs-lq-two-point-bounds-walk-rate
kind: claim
title: An l^q summable two-point function bounds the walk connectivity by rho to the power 2n/q
distinct_from:
  fpbs-sphere-two-point-rate-bounds-walk-rate: that bounds lambda(p) by rho cosh of the sphere-mass growth rate, which exceeds rho on all of (p_c, p_2] on trees; this bounds a_n(p) through l^q summability of tau_p(o,.) and gives exactly rho on the whole range p <= p_2.
  fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels: that assumes the operator gap p_c < p_{2->2}; this needs only the vector tau_p(o,.) in l^q, with no operator boundedness.
  fpbs-all-parameter-finite-cluster-spectrum: that bounds the finite-cluster part of a_n; this bounds all of a_n, infinite clusters included.
artifacts:
  - research/artifacts/fpbs/docs/lq-two-point-walk-rate-2026-09-17.md
  - experiments/lq-two-point-walk-rate-2026-09-17/tree_check.py
---

**ESTABLISHED (written deduction, Sections 2–3 of the artifact).**

Let `G` be a connected, locally finite, transitive graph. Let `rho = ||P||`,
`a_n(p) = P_p(o <-> X_n)` and `lambda(p) = lim a_n^(1/n)`. Put
`Z_q(p) = sum_x tau_p(o,x)^q` and `p_q = sup{p : Z_q(p) < infinity}`.

**Claim.**

1. If `q >= 2` and `p <= p_q`, then `a_n(p) <= rho^(2n/q)` for all `n`, with
   constant 1. So `lambda(p) <= rho^(2/q)`.
2. `lambda(p) = rho` for every `p <= p_2`. This is Hutchcroft's
   `p <= p_{2->2}` bound (arXiv:1804.10191v3, prop:nonuniquenessatpell2)
   extended to the possibly larger range `p <= p_2`.
3. `p_{2->2} <= p_2 <= p_q <= p_u` for every finite `q >= 2`, when `rho < 1`.

**Proof in one line.** Hölder gives `a_n <= ||p_n(o,.)||_{q'} Z_q^(1/q)`.
Log-convexity between `l^1` and `l^2` gives `||p_n(o,.)||_{q'} <= rho^(2n/q)`,
using `||p_n(o,.)||_2^2 = p_{2n}(o,o)`. Supermultiplicativity of `a_n`
(Harris-FKG) then removes the constant. Left-continuity of `tau_p(o,x)`
covers the endpoint `p = p_q`.

The tree check (`tree_check.out`, exit 0) confirms the bound with constant 1
on `T_3`, `T_4` and `T_6` for `n <= 400`, and shows it is sharp on `[0, p_2]`.

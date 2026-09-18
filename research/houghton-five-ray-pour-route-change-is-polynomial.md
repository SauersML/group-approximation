---
rg: 2
id: houghton-five-ray-pour-route-change-is-polynomial
kind: claim
title: "For n >= 5, changing the route ray of a Houghton pour of size m costs area O(m^(log_2 5))"
artifacts:
  - research/artifacts/zp-houghton-five-rays-2026-09-17.md
  - experiments/houghton-five-rays-2026-09-17/verify_splitting.py
distinct_from:
  houghton-far-commutation-has-quadratic-log-area-for-six-rays: that bounds route changes by m^2 log m using two auxiliary rays, so it needs n >= 6; this uses one auxiliary ray, so it holds for n >= 5, with exponent log_2 5.
---

Let `n >= 5`. Work in the finite presentation `P` of `H_n` from
`research/artifacts/zp-houghton-pours-2026-09-17.md` §0 (Lee's presentation plus the
letters `λ_xy`, `τ_x` and all trivial words of length `<= 40` in them). For
distinct rays `a,b,c` put `E^c_(a,b)(m) = λ_ac^m λ_cb^m`. As a permutation this is
independent of `c`. Let

```text
W(m) = max { Area( E^c_(a,b)(m) · E^d_(a,b)(m)^(-1) ) : a,b,c,d distinct rays }.
```

Then:

- `W(m_1 + m_2) <= 3W(m_1) + 2W(m_2) + 4m_1m_2 + 4m_1` (Lemma A);
- `W(m) <= 45 m^(log_2 5)` for all `m >= 1` (Proposition B).

Consequently, rerouting a transposition pushed `k` steps down a ray costs
`≼ k^(log_2 5)`. So does the far commutation `[α, α^(g_1^(-k))]`.

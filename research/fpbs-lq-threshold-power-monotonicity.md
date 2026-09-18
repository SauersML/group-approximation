---
rg: 2
id: fpbs-lq-threshold-power-monotonicity
kind: claim
title: The l^q thresholds of the two-point function satisfy p_q' at most p_q to the power q/q', so the whole l^q scale is one exponent q_0
distinct_from:
  fpbs-lq-two-point-bounds-walk-rate: that turns l^q summability at one p into a walk-rate bound; this compares different exponents q and parameters p with each other through the thinning inequality, and says nothing about rho.
  fpbs-normal-coset-fibre-mass-power-improvement: that imports thinning to improve fibre masses over a normal subgroup; this applies it to the global two-point function and derives the threshold calculus p_q' <= p_q^(q/q').
  fpbs-two-point-lq-threshold-gap-universal: that is the open hole p_c < p_q for all q > 2; this proves it is equivalent to q_0 <= 2 and that thinning transfer between parameters cannot prove it.
artifacts:
  - research/artifacts/fpbs/docs/lq-threshold-power-monotonicity-2026-09-17.md
  - experiments/lq-threshold-power-2026-09-17/check_thinning.py
---

**ESTABLISHED (written deduction, Sections 2–5 of the artifact).**

Let `G` be a connected, locally finite, transitive graph, with
`Z_q(p) = sum_x tau_p(o,x)^q`, `p_q = sup{p : Z_q(p) < infinity}` and
`q_0 = inf{q >= 1 : p_q > p_c}`.

**Claim.**

1. **Thinning.** `tau_(p^g)(x,y) >= tau_p(x,y)^g` for `p, g in [0,1]`.
2. **Power monotonicity.** `p_(q') <= p_q^(q/q')` for `1 <= q < q'`, so
   `q -> p_q^q` is nonincreasing.
3. **Calibration.** `p_1 = p_c`, hence `p_(2->2) <= p_2 <= sqrt(p_c)` and
   `p_q <= p_c^(1/q)`. The map `q -> p_q` is continuous. On `T_d` every
   inequality is an equality, with `p_q = p_c^(1/q)` and `q_0 = 1`.
4. **One exponent.** `{q : p_q > p_c} = (q_0, infinity)`. So the hole
   `fpbs-two-point-lq-threshold-gap-universal` ([Q]: `p_c < p_q` for all
   `q > 2`) holds iff `q_0 <= 2`, and `p_c < p_2` holds iff `q_0 < 2`.
5. **Obstruction.** Transporting `Z_q(p') < infinity` from one `p' > p_c`
   down to `(p_c, p')` by thinning proves exactly
   `q_0 <= q log(1/p')/log(1/p_c)`. Inputs good enough to give [Q] with
   strict inequality exist iff `q_0 < 2`. So this class, monotone
   power-coupling between parameters, dies at the exponent
   `log p/log p'`. That exponent is exact on trees, where thinning is an
   equality.

The only imports are the Duminil-Copin–Tassion finite-set criterion and BK,
both quoted as in existing ESTABLISHED routes. They give `chi_p < infinity`
for `p < p_c`. The thinning inequality is proved self-contained.
`check_thinning.py` (exit 0; output in `check_thinning.out`) checks thinning
by exact enumeration and checks the tree calibration.

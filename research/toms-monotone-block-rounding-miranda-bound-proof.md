---
rg: 2
id: toms-monotone-block-rounding-miranda-bound-proof
kind: route
title: Slack bounds each copy's delay, Poincare-Miranda for open sets finds an all-wall point, and the jump there costs K lines
target: toms-monotone-block-rounding-obeys-a-miranda-granularity-bound
requires: []
---

Imports from arXiv:2606.12188v2: the Section 4 construction, so
`X_M = (X_n)^K x P` with copy maps the coordinate projections, and a
pushforward has fibre rank `sum_b rank a(w^(b))`. Lemma 2: for `x in X_m` there is
a trace with stage-`m` measure `delta_x`, so `d(a_m) -> f` uniformly with
`d(a_m) <= f` gives the pointwise sandwich with `eps_m = sup_tau (f - d(a_m))`.

**Step 1 (Poincare–Miranda for open sets).** Let `V_1..V_K` be relatively open
in `Q = [0,1]^K`, with `{t_b = 1} ⊂ V_b` and `V_b ∩ {t_b = 0} = ∅`. Then some
`t* in Q` lies in no `V_b` and in the closure of `∩_b V_b`.
- Put `u_b(t) = dist(t, Q \ V_b) - dist(t, V_b)`. It is continuous, `> 0` on `V_b`
  and `<= 0` off `V_b`. Let `m_b > 0` be its minimum on the compact face
  `{t_b = 1} ⊂ V_b`. Fix `0 < eta < min(1/2, min_b m_b)` and put
  `y = (eta, ..., eta)`, `Lambda(t)_b = t_b - 1/2`.
- On `{t_b = 0}`: `u_b <= 0 < eta` and `Lambda_b = -1/2 < eta`. On `{t_b = 1}`:
  `u_b >= m_b > eta` and `Lambda_b = 1/2 > eta`. So the straight-line homotopy from
  `u` to `Lambda` avoids `y` on the boundary, and `deg(u, Q°, y) = deg(Lambda, Q°, y) = 1`.
- Hence some `t_eta` has `u(t_eta) = y`, so `t_eta in ∩_b V_b`. A limit point `t*`
  of `t_eta` as `eta -> 0` has `u(t*) = 0`, so `t*` lies in no `V_b`.

**Step 2 (path product).** `X_n` is connected, and `F_n` attains `min h` and
`max h` (put every leaf at an extremum of `h`). Let `gamma` be a path from a
minimum to a maximum. Fix `p_0 in P` and let `sigma(t) in X_M` have copy
coordinates `gamma(t_b)` and `P`-coordinate `p_0`. Write `rank_b(w)` for the
fibre rank of `Q_b a_M Q_b` at `w`.

**Step 3 (budget).** Since `r_M F_M(w) = sum_b r_n F_n(w^(b))` and `a_M` is
block-diagonal,

```text
rank_b(w) = R_M(w) - sum_(b' != b) rank_b'(w) <= r_M F_M(w) - sum_(b' != b) R_n(w^(b'))
          <= r_n F_n(w^(b)) + (K - 1) r_n eps_n,
rank_b(w) >= R_n(w^(b)) >= r_n F_n(w^(b)) - r_n eps_n.
```

**Step 4 (walls).** The interval
`[r_n (min h + (K-1) eps_n), r_n (max h - eps_n) - 1]` has length
`r_n (rho - K eps_n) - 1 >= 1`, so it contains an integer `k`. Put
`V_b = { t : rank_b(sigma(t)) >= k + 1 }`, open because fibre rank is lower
semicontinuous. On `{t_b = 1}` Step 3 gives `rank_b >= r_n (max h - eps_n) >= k + 1`.
On `{t_b = 0}` it gives `rank_b <= r_n (min h + (K-1) eps_n) <= k`.

**Step 5 (the jump).** Step 1 gives `t*` and `t_j -> t*` with
`rank_b(sigma(t_j)) >= k + 1` and `rank_b(sigma(t*)) <= k` for every `b`. The upper
band at `sigma(t_j)` gives `K (k + 1) <= r_M F_M(sigma(t_j))`, hence
`K (k + 1) <= r_M F_M(sigma(t*))` by continuity. The lower band at `sigma(t*)` gives
`K k >= R_M(sigma(t*)) >= r_M F_M(sigma(t*)) - r_M eps_M >= K (k + 1) - r_M eps_M`.
So `eps_M >= K / r_M = 1/r_n`.

**Step 6 (corollary).** Suppose `eps_m <= C r_m^(-gamma)` for `m >= m_0`, with
`gamma > 0`.
- For large `M`, let `n` be the least integer `>= m_0` with
  `C r_n^(-gamma) 2^(M-n) <= rho/2`. The left side decreases in `n`, `n = M`
  qualifies for large `M`, and `n -> infinity` as `M -> infinity`.
- Then `K eps_n <= rho/2`, so `r_n (rho - K eps_n) >= r_n rho/2 >= 2` for large
  `M`, and the theorem gives `eps_M >= 1/r_n`.
- Minimality of `n` gives `2^(M-n) > rho r_(n-1)^gamma /(4C) >= c_0 r_n^gamma` with
  `c_0 = rho/(2^(2+gamma) C)`, so `r_M = r_n 2^(M-n) > c_0 r_n^(1+gamma)`.
- Therefore `C r_M^(-gamma) >= eps_M >= 1/r_n > (c_0 / r_M)^(1/(1+gamma))` for all
  large `M`. This forces `1/(1+gamma) >= gamma`, i.e. `gamma <= (sqrt 5 - 1)/2`.

**Step 7 (the line subalgebra).** In `D ≅ C(Omega)`, `b <~ c` iff the open
support of `b` lies in that of `c`. Supports of stage elements are unions of
open sets times single lines, and every line lies in one copy. So a
Cuntz-increasing sequence in `D` is block-diagonal with blockwise domination at
every pair of stages, and Steps 1–6 apply. Square.

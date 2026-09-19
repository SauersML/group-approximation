---
rg: 2
id: coboundary-flatness-test-proof
kind: route
title: A satisfied closed walk telescopes to trivial holonomy, so non-flat mass is at most congestion times violated mass, while coboundary expansion bounds it below by distance to coboundaries, which is exactly one minus the value; the windmill computes both constants exactly
target: coboundary-expanding-hosts-cannot-carry-shift-ugc
requires: []
artifacts:
  - experiments/ugc-coboundary-kill-2026-09-17/check_coboundary_test.py
  - experiments/ugc-coboundary-kill-2026-09-17/output.txt
---

Notation is as in the target claim. There are no imports.

**0. Value is distance to coboundaries.** For a labeling `x`, edge `e = (u, v)`
is satisfied iff `b_e = x_v x_u^(-1) = (dx)_e`. So the violated mass of `x` is
`mu_E{e : b_e != (dx)_e}`. Minimizing over `x` gives
`1 - val(b) = dist(b, B^1)`.

**1. Telescoping (upper bound of T1).** Traversing `e = (u, v)` backwards uses
`(dx)_e^(-1) = x_u x_v^(-1)`. So along any walk `v_0, ..., v_l` the factor
contributed by the step `v_(i-1) -> v_i` is `x_(v_i) x_(v_(i-1))^(-1)` in both
directions. Then `hol_(dx)(c) = x_(v_l) x_(v_0)^(-1) = 1` for a closed walk.
Fix an optimal `x` and set `F = {e : b_e != (dx)_e}`, so that
`mu_E(F) = 1 - val(b)`. If `c` traverses no edge of `F`, then
`hol_b(c) = hol_(dx)(c) = 1`. Hence

```text
nf_C(b) <= Pr_c[c traverses some e in F] <= E_c[# traversals of F]
         = sum_(e in F) m_C(e) <= M(C) mu_E(F) = M(C) (1 - val(b)).
```

This holds for every group, abelian or not.

**2. Lower bound of T1.** For `b` not in `B^1`, the definition of `beta_A(C)`
together with step 0 gives `nf_C(b) >= beta_A(C) dist(b, B^1) = beta_A(C) (1 - val(b))`.
For `b` in `B^1` both sides are `0`, by step 1.

**3. T2.** `nf_C(b)` is a sum over `supp C` of indicator values. Each needs at
most `max length` group multiplications and one identity test. `M(C)` is a
maximum over `E` of explicit ratios. On a YES instance, `val >= 1 - eps`, and
step 1 gives `nf <= M eps`, so the test accepts. On a NO instance,
`val <= delta`, and step 2 gives `nf >= beta (1 - delta)`. Since
`kappa eps < 1 - delta` means `M eps < beta (1 - delta)`, the test rejects.
The algorithm never uses `beta` and never uses `A` beyond multiplication, so it
is uniform in `A`.

**4. T2'.** Compose `f`, the map `x -> C_x`, and the test of step 3. Every
output satisfies `kappa <= K` and `K eps < 1 - delta`, so the composition
decides `L` in polynomial time. For the UGC reading: fix `delta`. NP-hardness
at `(1 - eps, delta)` with the shape of T2' needs `K >= (1 - delta)/eps`, which
is unbounded as `eps -> 0`.

**5. Windmill (T3).** Take `W_s(eta)` and `C` uniform on the `s` triangles
`t_i = (a, u_i, v_i)`, with `0 < eta < 2/3`.

* *Congestion.* Each edge lies on exactly one triangle and is traversed once,
  so `m_C = 1/s` on every edge. The ratios are `1/(1 - eta)` on `u_i v_i` and
  `2/eta` on apex edges. So `M = 2/eta`, because `eta < 2/3`.
* *Distance.* Let `N` be the number of non-flat triangles. The triangles are
  edge-disjoint and every coboundary is flat on each of them, by step 1. So
  any `dx` differs from `b` on at least one edge of each non-flat triangle, and
  `dist >= N eta/(2s)`, the least edge weight, because `eta/2 <= 1 - eta`.
  Conversely, put `x_a = 1`. On a flat `t_i`, put `x_(u_i) = b_(a u_i)` and
  `x_(v_i) = b_(a v_i)`. Flatness,
  `b_(a v_i)^(-1) b_(u_i v_i) b_(a u_i) = 1`, is exactly satisfaction of
  `u_i v_i`. On a non-flat `t_i`, put `x_(u_i) = b_(a u_i)` and
  `x_(v_i) = b_(u_i v_i) x_(u_i)`, which violates only `a v_i`. So
  `dist = N eta/(2s)`.
* *Expansion.* `b` is not in `B^1` iff `N >= 1`, and then
  `nf/dist = (N/s)/(N eta/(2s)) = 2/eta`. So `beta_A = 2/eta` and `kappa_A = 1`
  for every finite group `A`.
* *Spectrum.* The total weight is `1`. Let `f` vanish at `a`, and put
  `f(u_i) = f(v_i) = y_i` with `sum_i y_i = 0`; these `f` form an
  `(s - 1)`-dimensional space. The Dirichlet form is `(eta/s) sum y_i^2`, and
  the degree norm is `((2 - eta)/s) sum y_i^2`. So every Rayleigh quotient in
  this space equals `eta/(2 - eta)`. This space is orthogonal, in the degree
  inner product, to the constants, because `sum_v deg(v) f(v) = ((2 - eta)/s) sum y_i = 0`.
  Adding the ground state gives an `s`-dimensional space on which the quotient
  is at most `eta/(2 - eta)`. By Courant--Fischer, `lambda_2, ..., lambda_s` are
  all at most `eta/(2 - eta)`.
* *Converse.* With girth `> r`, every closed walk of length `<= r` reduces to
  the empty walk by cancelling backtracks `e e^(-1)`. A nontrivial cyclically
  reduced closed walk would contain a cycle of length `<= r`. Each cancellation
  preserves holonomy, so every such walk has trivial holonomy for every `b`,
  and `nf = 0` while `dist > 0` for any `b` not in `B^1`. Such `b` exist
  whenever the cycle rank is positive. So `beta = 0` and `kappa = infinity`.

**6. T4.** On `K_m` with alphabet `{1, 2, 3}` and every constraint
`sigma_v = (2 3) sigma_u`, the labeling `sigma = 1` satisfies every edge.
Every oriented triangle has holonomy `(2 3)^3 = (2 3) != 1`, because
`(2 3)^(-1) = (2 3)`. So `nf = 1` at value `1`, and no bound
`nf <= M (1 - val)` holds for general unique games.

**7. Computation.** `check_coboundary_test.py` recomputes `M`, `beta` and
`lambda_2` over `Z_2` by brute force over all cochains and gauges for
`K_4 x K_2`, two `K_4` joined by a bridge, cones over `K_3 + K_3` with both
cycle systems, and Petersen. It checks step 1 exactly on 2 x 2000 planted
`S_3`-shift games. The maximum of `nf - M viol` is `0`. The output is in
`output.txt`.

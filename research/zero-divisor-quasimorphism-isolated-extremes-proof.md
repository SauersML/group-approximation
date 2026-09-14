---
rg: 2
id: zero-divisor-quasimorphism-isolated-extremes-proof
kind: route
title: Evaluate the quasimorphism along the positive relation at an isolated extreme point
target: zero-divisor-supports-have-no-quasimorphism-isolated-extremes
requires:
  - zero-divisor-support-vertex-cones-contain-positive-relations
---

Let `phi` be homogeneous with defect `D`.

(1) **Basic facts.** `phi(1) = phi(1^2) = 2 phi(1)`, so `phi(1) = 0`, and
`phi(g^-1) = -phi(g)` by homogeneity with `m = -1`. By induction on `k`,
`|phi(u_(k-1) ... u_0) - sum_i phi(u_i)| <= (k-1) D`.

(2) **Positive relations are not quasi-positive.** Let `P <= G` and suppose
`u_(k-1) ... u_0 = 1` with `k >= 1` and all `u_i in P`. If `phi(u) > D` for
all `u in P`, then by (1)
`0 = phi(1) >= sum_i phi(u_i) - (k-1) D > k D - (k-1) D = D >= 0`, a
contradiction. Likewise `phi(u) < -D` for all `u in P` is impossible.

(3) **Left zero divisors.** By
`zero-divisor-support-vertex-cones-contain-positive-relations`, for every
`a in A` there is a positive relation among the elements of
`U_a = {c^-1 a : c in A, c != a}`. For `u = c^-1 a`,
`|phi(u) - phi(c^-1) - phi(a)| <= D` gives
`phi(a) - phi(c) - D <= phi(u) <= phi(a) - phi(c) + D`.
- If `phi(c) - phi(a) > 2D` for all `c != a`, then `phi(u) < -D` on `U_a`,
  contradicting (2).
- If `phi(a) - phi(c) > 2D` for all `c != a`, then `phi(u) > D` on `U_a`,
  contradicting (2).

(4) **Right zero divisors.** If `beta alpha = 0` then `alpha^* beta^* = 0` for
the anti-automorphism `(sum r_g g)^* = sum r_g g^-1`, so `alpha^*` is a left
zero divisor with support `A^-1`. Its difference sets are
`{c a^-1 : c in A, c != a}`, as recorded in consequence 3 of the positive
relations node. For `u = c a^-1`,
`phi(c) - phi(a) - D <= phi(u) <= phi(c) - phi(a) + D`, and the two cases of
(3) run with the roles of the inequalities exchanged: an isolated minimum `a`
gives `phi(u) > D` on the difference set, an isolated maximum gives
`phi(u) < -D`. Both contradict (2).

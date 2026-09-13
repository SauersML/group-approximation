---
rg: 2
id: zero-divisor-vertex-cone-positive-relation-proof
kind: route
title: Follow the second expression of each product from one support point until the walk closes
target: zero-divisor-support-vertex-cones-contain-positive-relations
requires: []
---

Let `B = supp beta` and fix `a in A`.

(1) **A second expression.** For `b in B` the coefficient of `ab` in
`alpha beta` is the sum of `alpha_c beta_(b')` over the pairs
`(c, b') in A x B` with `c b' = ab`. It is `0`, and the pair `(a, b)`
contributes `alpha_a beta_b != 0`. So some other pair `(c, b')` has
`c b' = a b`. Then `c != a`, since `c = a` gives `b' = b`. Choose one such
pair for each `b` and write `c(b)` and `p(b) = c(b)^-1 a b in B`.

(2) **A closed walk.** `B` is finite, so iterating `p` from any point reaches
a cycle `b_0, b_1 = p(b_0), ..., b_k = b_0` with `k >= 1`. Put
`c_i = c(b_i)` and `u_i = c_i^-1 a in U_a`. Then `b_(i+1) = u_i b_i`, so

```text
u_(k-1) ... u_1 u_0 b_0 = b_0,   hence   u_(k-1) ... u_1 u_0 = 1.
```

(3) **Two letters.** If all `c_i` equal one `c`, the relation reads
`(c^-1 a)^k = 1` with `c^-1 a != 1`, a nontrivial torsion element. `G` is
torsion-free, so at least two distinct `u_i` occur, and `k >= 2`.

(4) **Consequence 1.** If `u(Y)` is a proper subset of `Y` for all
`u in U_a`, then `w = u_(k-1) ... u_0` has `w(Y) <= u_(k-1)(Y)`, a proper
subset of `Y`, so `w` is not the identity of `X`. This contradicts (2).

(5) **Consequence 2.** A closed convex cone `C` with nonempty interior and no
line has boundary points other than `0`. So the interior of `C` is a proper
subset of `Y = C \ {0}`, and (4) applies. The nonnegative orthant is such a
cone, and a matrix with positive entries maps it minus `0` into its
interior.

(6) **Consequence 3.** `(beta alpha)^* = alpha^* beta^*` for
`(sum r_g g)^* = sum r_g g^-1`, and `supp alpha^* = A^-1`. The set `U_(a^-1)`
for `A^-1` is `{ c a^-1 : c in A, c != a }`.

(7) **Consequence 5.** If `phi(a) <= phi(c)` for all `c in A`, left invariance
gives `phi(u) = phi(c)^-1 phi(a) <= 1` for `u = c^-1 a`. Put
`w_i = phi(u_(k-1) ... u_i)`. Then `w_i <= w_(i+1)`, strictly when
`phi(u_i) < 1`, and `w_(k-1) <= 1`. Since `w_0 = phi(1) = 1`, every
`phi(u_i) = 1`, that is `phi(c_i) = phi(a)`. By (3) at least two distinct
`c_i` occur, so the minimum is attained at least three times.

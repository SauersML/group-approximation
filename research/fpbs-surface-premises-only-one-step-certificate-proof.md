---
rg: 2
id: fpbs-surface-premises-only-one-step-certificate-proof
kind: route
title: Build the minimal admissible norm profile from anchor values by per-generator subadditivity of the sprinkling rate
target: fpbs-surface-premises-only-one-step-certificate
requires: []
---

Notation is as in the target. Every `A_u` is an entrywise nonnegative
operator with `||A_u|| <= 2`. So each `R(p,p')` is an entrywise nonnegative
kernel, and it depends continuously on `(p,p')` in operator norm, since
`||R|| <= 2 sum_u r_u`.

**Fact N (nonnegative kernels).** If `0 <= K <= K'` entrywise, then
`||K|| <= ||K'||`. Indeed `||K|| = sup ||K f||` over `f >= 0` with `||f|| = 1`,
because `|K f| <= K |f|`, and `K f <= K' f` pointwise for `f >= 0`.

**Step 1 (floor contains the conclusion).** `inf_t phi(gamma(t)) <= phi(gamma(1)) = phi(e)`.

**Step 2 (per-generator subadditivity).** For `x, y, z` in `[0,1-eps]` with
`y <= z`, put `r(s,s') = (s'-s)/(1-s)` for `s <= s'`. We claim

```text
r(x, x v z)  <=  r(x, x v y) + r(y, z).
```

* If `z <= x`, the left side is `0`.
* If `x <= y`, the left side is `(z-x)/(1-x) = (y-x)/(1-x) + (z-y)/(1-x)`, and
  `(z-y)/(1-x) <= (z-y)/(1-y)` because `1-y <= 1-x`.
* If `y < x < z`, the left side is `f(x)` and the right side is `f(y)`, where
  `f(s) = (z-s)/(1-s)`. Since `f'(s) = (z-1)/(1-s)^2 < 0`, `f(x) <= f(y)`.

Apply this for every `u`, multiply by `A_u >= 0` and sum. Entrywise,
`R(a, a v p') <= R(a, a v p) + R(p,p')` for `p <= p'`. By Fact N and the
triangle inequality,

```text
||R(a, a v p')||  <=  ||R(a, a v p)|| + ||R(p,p')||.          (*)
```

**Step 3 (`Phi_(a,c)` is admissible).**

* **(M):** for `p <= p'`, each coordinate of `R(a, a v p)` is at most the
  corresponding coordinate of `R(a, a v p')`. By Fact N the norm increases, so
  `Phi` decreases.
* **(L):** if `Phi_(a,c)(p) = 0` there is nothing to prove. Otherwise, by (*),
  `Phi_(a,c)(p) - ||R(p,p')|| = c - ||R(a,a v p)|| - ||R(p,p')||`, which is at
  most `c - ||R(a, a v p')||`, which is at most `Phi_(a,c)(p')`.
* **(C):** this follows from the continuity of `p -> R(a, a v p)` in operator
  norm.
* **Anchor value:** `R(a,a) = 0`, so `Phi_(a,c)(a) = c`.

For maxima of admissible functions:

* (M) and (C) are preserved.
* (L) holds because
  `max_i Phi_i(p') >= Phi_j(p') >= Phi_j(p) - ||R(p,p')||`, where `j` attains
  the maximum at `p`.

**Step 4 (exact content).**

* **If the certificate holds.** Suppose `c_i - ||R(a_i, a_i v e)|| > 0` for
  some `i`, and let `Phi` be admissible with `Phi(a_i) >= c_i`. By (L) with
  `p = a_i` and `p' = a_i v e`, `Phi(a_i v e) > 0`. By (M) and `e <= a_i v e`,
  `Phi(e) > 0`.
* **If the certificate fails for every `i`.** Then
  `Psi = max_i Phi_(a_i,c_i)` is admissible, has `Psi(a_i) >= c_i`, and has
  `Psi(e) = 0`. So no path argument that uses only (M), (L), (C) and the
  anchor values can reach `e`. Along any path from an anchor to `e`, the
  profile `Psi` passes the openness test and fails the floor.

**Step 5 (the route uses nothing else).** The route
`fpbs-dead-weighted-surface-continuity-l2` requires two claims.

* **`fpbs-one-edge-sprinkling-l2-lipschitz`:** the route uses item 1 only
  through item 2, which is (L), and item 4, which is (L) plus (C). Item 3 is
  the special case of (L) with the anchor on `S'` and `0` on `S''`, which is a
  one-step certificate.
* **`fpbs-uniform-floor-equivalence-restricted-to-monotone-paths`:** item 1 is
  the consequence of (M) that on monotone paths the floor equals the endpoint
  value. Item 2 bounds anchors on `Z^2`, which is a different graph.

Neither claim constrains `phi(e)` beyond (M), (L), (C). By Step 4, the
conjunction of the two gives `phi(e) > 0` only at generating sets where an
anchor passes the one-step certificate. That certificate is a separate
quantitative input and is not a prerequisite. Hence the route does not derive
`fpbs-critical-dyadic-projection-estimate`.

**Calibration.** On record, the one-step certificate from the explicit tree
anchor reaches `T_(2k) x Z` for `k >= 4`, and it reaches `F_2 x Z` only if
`p_c(T_4 x Z) < 0.21085`
(`fpbs-weighted-surface-continuity-reduces-to-uniform-floor`). So even
restricted to products, the route's reach is a finite list of numerical
checks, not a universal statement.

---
rg: 2
id: resolvent-ring-presentation-is-not-faithful-on-r-bar-proof
kind: route
title: A characteristic-l model with a q-cycle shift separates e x e from e x^q e
target: resolvent-ring-presentation-is-not-faithful-on-r-bar
requires:
  - rf-resolvent-ring-has-z-localized-corner
---

**δ = 0 in R̄_l.** In the component `M_r` of `R̄_l` (basis `f_j`, `j in Z/l^(r-1)`),
`e x^k e f_0 = e f_(-k)`. This is `f_0` if `l^(r-1)` divides `k`, and 0 otherwise.
Also `e x^k e f_j = 0` for `j != 0`. For `k = 1` and `k = q` the divisibility holds
exactly when `r = 1`, because `l != q`. So `e x e` and `e x^q e` have the same
components, and `δ = 0` in `R̄_l`.

**δ != 0 in R_l.** Let `V` be the `F_l`-vector space with basis `f_j`, `j in Z/q`.
Put `u = 0`, `x f_j = f_(j-1)`, `x' = x^(-1)`, `B = 1`, `e = ` the projection onto `f_0`.
The relations hold:
- `x x' = x' x = 1`;
- `x u = 0 = (u + l) x`, because `l = 0` in `F_l`;
- `B(u+1) = (u+1)B = 1`;
- `u e = e u = 0`;
- `e^2 = e`.

So this is a ring homomorphism `R_l -> End(V)`. Under it, `e x e = 0`, since
`x f_0 = f_(-1) != f_0` for `q >= 2`, and `e x^q e = e`, since `x^q = 1`. So
`δ -> -e != 0`. ∎

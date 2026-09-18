---
rg: 2
id: fpbs-worst-pair-connectivity-rate-kernel-proof
kind: route
title: Fekete on the Harris-FKG supermultiplicative worst connection, uniqueness forces theta squared, and a sphere sum dominates sphere size times the worst connection
target: fpbs-worst-pair-connectivity-rate-kernel
requires: []
---

Complete written proof. Notation as in the claim. No computation is used.

**Standard imports.**

- **Harris-FKG:** increasing events are positively correlated under a product
  measure. `{u <-> w}`, `{w <-> v}` and `{u <-> infinity}` are increasing.
- **Fekete:** if `a_(n+m) <= a_n + a_m` and `a_n >= 0`, then `a_n/n` converges
  to `inf_n a_n/n`.

**Item 1.** `tau_p(o,v) >= p^(d(o,v))`, so `0 < p^n <= kappa_p(n) <= 1`. Let
`d(u,v) <= n+m` and pick `w` on a geodesic with `d(u,w) <= n` and
`d(w,v) <= m`. Then `{u <-> w} ∩ {w <-> v}` is contained in `{u <-> v}`.
Harris-FKG gives

```text
tau_p(u,v) >= tau_p(u,w) tau_p(w,v) >= kappa_p(n) kappa_p(m).
```

Put `a_n = -log kappa_p(n)`. Then `a_n` is subadditive and lies in
`[0, n log(1/p)]`, so Fekete gives existence and `0 <= gamma(p) <= -log p`.

- **Minimum over a finite ball.** By transitivity the infimum is a minimum over
  the finite set `B_n`.
- **Monotonicity.** `tau_p` is nondecreasing in `p` (standard monotone
  coupling), hence so is each `kappa_p(n)`, and `gamma` is nonincreasing.
- **Semicontinuity.** Write `tau_p(o,v) = sup_R P_p(o <-> v in B_R)`, a
  supremum of polynomials. So `tau_p(o,v)` is lower semicontinuous, and
  `-log tau_p(o,v)` is upper semicontinuous. Then `a_n(p)/n`, a maximum of
  finitely many such functions, is upper semicontinuous. So is `gamma`, an
  infimum of upper semicontinuous functions.
- **Left-continuity.** `gamma` is nonincreasing, so `gamma(p-) >= gamma(p)`.
  Upper semicontinuity gives `gamma(p) >= gamma(p-)`.

**Item 2.** Let `p' <= q` and suppose that `P_(p')`-a.s. there is exactly one
infinite cluster. Then `theta(p') > 0`. If `u` and `v` both lie in infinite
clusters they lie in the same one, so by Harris-FKG

```text
tau_(p')(u,v) >= P_(p')(u <-> infinity, v <-> infinity) >= theta(p')^2.
```

So `kappa_(p')(n) >= theta(p')^2` for every `n`, and `gamma(p') = 0`. Item 1
gives `gamma(p') >= gamma(q) > 0`, a contradiction.

**Item 3.**

- **Sphere sum.** `E_p|K_o ∩ S_r| = sum_(x in S_r) tau_p(o,x) >= |S_r| kappa_p(r)`.
- **Spheres grow at rate `gr`.** `|B_R| <= (R+1) max_(j <= R) |S_j|`. Let
  `j_R <= R` attain the maximum. Then `|S_(j_R)|` grows without bound, so
  `j_R -> infinity`. Once `|B_R| >= R+1`,
  `|S_(j_R)|^(1/j_R) >= (|B_R|/(R+1))^(1/R) -> gr`. Hence
  `limsup_r (1/r) log|S_r| >= log gr`.
- **Combining.** `(1/r) log kappa_p(r)` converges to `-gamma(p)`, and adding a
  convergent sequence commutes with `limsup`. So
  `g(p) >= limsup_r (1/r) log|S_r| - gamma(p) >= log gr - gamma(p)`.

**Item 4.**

- `(K) => p_c < p_u`: take `q = p > p_c` in item 2. No `p' <= p` is in the
  uniqueness phase, so `p_u >= p > p_c`.
- `(K') => (K)`: this is item 3.
- `(G) => (K')`: `(G)` gives `g(p) < arccosh(1/rho) <= log gr` at some
  `p > p_c`. The last inequality is "Consistency at p = 1" in Section 4 of the
  gauge-certificates artifact: `lambda(1) = 1`, `g(1) = log gr` and Theorem 3.2
  there give `1 <= rho cosh(log gr)`.
- `(EG) => (G)`: this is Section 4 of the same artifact.

**Item 5.** On `T_d`, `tau_p(o,v) = p^|v|`, so `kappa_p(n) = p^n` and
`gamma(p) = -log p > 0` for `p < 1`. Also `|S_r| = d(d-1)^(r-1)`, so
`g(p) = log((d-1)p) < log(d-1) = log gr` exactly when `p < 1`. The range of
(G) is Section 4 of the artifact.

**Item 6.** `gamma = inf_n a_n/n`, so `gamma(p) <= a_N(p)/N` for every single
`N`, while `gamma(p) >= c` is equivalent to `a_n(p) >= cn` for all `n`. QED.

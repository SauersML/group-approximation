---
rg: 2
id: fpbs-flat-rate-point-exceeds-l2-point-on-free-products
kind: claim
title: On Z/2 * Z/2 * Z/3 and four other free products of Z/2's and Z/3's the flat-rate point strictly exceeds the l2 point
distinct_from:
  fpbs-flat-rate-point-equals-l2-point: that conjectures p_* = p_2 on every nonamenable Cayley graph; this proves p_* > p_2 on five explicit free products, refuting it.
  fpbs-lq-two-point-bounds-walk-rate: that proves p_2 <= p_* on every transitive graph; this shows that inequality can be strict and identifies p_* exactly on the examples.
  fpbs-flat-walk-rate-past-pc-universal: that is the open hole p_c < p_* on every nonamenable Cayley graph; this computes p_* on graphs where p_c < p_* is already known, and shows only that the hole is not the l2 statement in disguise.
  fpbs-free-product-cayley-graphs-have-critical-l2-gap: that proves p_c < p_{2->2} on free products; this compares two larger thresholds, p_2 and p_*, on a subclass.
  fpbs-green-visit-criterion-universal: that pairs tau_p with the Green function at z = 1; this pairs it with G_z for every z up to the spectral radius, which characterizes p_* exactly.
artifacts:
  - research/artifacts/fpbs-free-product-flat-rate-2026-09-18.md
  - experiments/fpbs-green-weighted-flat-rate-2026-09-17/free_product_thresholds.py
  - experiments/fpbs-green-weighted-flat-rate-2026-09-17/free_product_thresholds.out
  - experiments/fpbs-green-weighted-flat-rate-2026-09-17/certify_a_ne_b.py
  - experiments/fpbs-green-weighted-flat-rate-2026-09-17/certify_a_ne_b.out
---

**ESTABLISHED** (written proof in the artifact, plus an exact rational
certificate). Let

```text
G = Cay((Z/2)^{*k} * (Z/3)^{*m}, {x_i} ∪ {r_j^{±1}})
```

for `(k,m)` in `{(2,1), (3,1), (1,2), (2,2), (4,1)}`. Use the notation of
`fpbs-flat-rate-point-equals-l2-point`:

- `lambda(p) = lim (E tau_p(o,X_n))^(1/n)`;
- `p_* = sup{p : lambda(p) = rho}`;
- `p_2 = sup{p : sum_x tau_p(o,x)^2 < infinity}`.

Then

```text
p_*  >  p_2.
```

For `Z/2 * Z/2 * Z/3` (degree 4), in floating point and not certified:

- `p_c = 0.36046`;
- `p_2 = 0.5736456`;
- `p_* = 0.5737271`.

So the gap is about `8e-5`. Only its sign is proved.

**What is proved, in order.**

1. **Any transitive graph.** `sum_n a_n(p) z^n = sum_x G_z(o,x) tau_p(o,x)`.
   So `lambda(p) = 1/(radius of convergence)`, and
   `p_* = sup{p : sum_x G_z(o,x) tau_p(o,x) < infinity for all z < 1/rho}`.
2. **These free products.** `tau_p` and `G_z` factor over the letters of the
   normal form, since the prefixes are cut vertices of a block graph. The sum
   over reduced words with factor weights `u_2, u_3` is finite iff
   `Phi = k u_2/(1+u_2) + m u_3/(1+u_3) < 1`. This gives
   `p_* = p_G`, the root of `Phi(a(R)p, 2F(R)q(p)) = 1`, where:
   - `q = p + (1-p)p^2`;
   - `a` and `F` are the first-passage generating functions to a generator
     at `R = 1/rho`.
3. **Convexity.** The region `{Phi(e^s) < 1}` is convex, by Cauchy–Schwarz on
   the word sum. The Green point `A = (log a(R)^2, log 2F(R)^2)` lies in its
   closure, because `sum_x G_z(o,x)^2 < infinity` for `z < R`. The l2 point
   `B = (log p_2^2, log 2q(p_2)^2)` lies on its boundary.
4. **Strictness.** The boundary curve is analytic and not affine when
   `(k,m) != (1,1)`. So the midpoint of `A` and `B`, which is exactly
   `(log a(R)p_2, log 2F(R)q(p_2))`, is interior unless `A = B`. That gives
   `p_G > p_2`.
5. **Certificate.** `A != B`. If `A = B`, then `(p_2, q(p_2))` would solve
   both first-step equations with a common `z`. Exact rational enclosures
   show the two values of `z` differ, for example `1.0682` against `1.1274`
   for `(2,1)`.

**Scope.**

- On `T_d` and on `PSL_2(Z) = Z/2 * Z/3` the same computation gives
  `p_* = p_2`: there is one block type in the first case, and an affine
  boundary in the second. The equality in the target's radial evidence is
  therefore special to one-type geometry.
- These graphs already satisfy `p_c < p_2 < p_u = 1`, so this gives no new
  case of Benjamini–Schramm. It shows that the flat-rate hole [F]
  (`p_c < p_*`) is a genuinely weaker graph property than `p_c < p_2`.

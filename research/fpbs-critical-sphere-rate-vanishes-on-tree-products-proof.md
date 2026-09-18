---
rg: 2
id: fpbs-critical-sphere-rate-vanishes-on-tree-products-proof
kind: route
title: Distance types of a product of trees make the sphere rate a supremum of lower semicontinuous functions, each nonpositive below p_c
target: fpbs-critical-sphere-rate-vanishes-on-tree-products
requires: []
---

Complete written proof. Notation as in the claim. No computation is used.

**Standard imports.**

- **Harris-FKG** for increasing events under product measure.
- **Monotone coupling:** `tau_p(u,v)` is nondecreasing in `p`.
- **Sharpness (Menshikov; Aizenman-Barsky):** on a transitive graph,
  `chi_p = E_p|K_o| < infinity` for every `p < p_c`.
- **`g(p_c) >= 0`** is established in the graph (Corollary 2.4 of
  `research/artifacts/fpbs/docs/gauge-certificates-and-sphere-rate-2026-09-17.md`,
  as recorded in `fpbs-sphere-two-point-rate-right-continuous-universal`).

**Step 0 (types).** `Aut(T_d)` is transitive on ordered pairs of vertices at
distance `k`, for every `d >= 2` and `k >= 0`. The product of factor
automorphisms is an automorphism of `G`. Bernoulli percolation is invariant
under `Aut(G)`. So `tau_p(u,w)` depends only on the vector `v` of factor
distances between `u` and `w`. Write it `tau_p(v)`.

The number of vertices at type `v` from `o` is
`N(v) = prod_i |S^(T_(a_i))_(v_i)|`, where `|S_0| = 1` and
`|S_j| = a(a-1)^(j-1)` for `j >= 1`. Hence

```text
W(v) <= N(v) <= c W(v),     c = prod_i a_i/(a_i - 1),
```

and `M_r(p) = sum_(|v|=r) N(v) tau_p(v)`.

**Step 1 (supermultiplicativity along a type).** Fix `v`. In each factor fix a
geodesic ray from `o`, which exists because `a_i >= 2`. Let `z_j` be the vertex
whose `i`-th coordinate is the point at distance `j v_i` on the `i`-th ray.
Then `z_j` has type `j v` from `o`, and `z_(j+1)` has type `v` from `z_j`. The
event `{o <-> z_J}` contains the intersection of the events
`{z_j <-> z_(j+1)}`. Harris-FKG gives

```text
tau_p(J v) >= tau_p(v)^J.
```

**Step 2 (type formula).** Put `h_v(p) = (1/|v|) log(W(v) tau_p(v))` and
`H(p) = sup_(v != 0) h_v(p)`. For `p > 0`, `tau_p(v) >= p^|v| > 0`. Also
`h_v <= log max_i (a_i - 1)`. So `H` is finite.

- **Lower bound.** Step 1 and `N >= W` give
  `M_(J|v|) >= N(Jv) tau_p(Jv) >= (W(v) tau_p(v))^J = e^(J|v| h_v(p))`. So
  `g(p) >= h_v(p)` for every `v`, and `g >= H`.
- **Upper bound.** For `|v| = r`, `N(v) tau_p(v) <= c W(v) tau_p(v) = c e^(r h_v) <= c e^(rH)`.
  There are at most `(r+1)^n` types with `|v| = r`, so
  `M_r <= c (r+1)^n e^(rH)` and `g <= H`.

**Step 3 (left-continuity).** Write `tau_p(v) = sup_R P_p(o <-> z within B_R)`.
This is a supremum of polynomials in `p`, each nondecreasing on `[0,1]`. So
`p -> tau_p(v)` is lower semicontinuous and nondecreasing, and so is each
`h_v` on `(0,1]`. Then `H` is lower semicontinuous and nondecreasing, being a
supremum of such functions. A nondecreasing lower semicontinuous function is
left-continuous:

```text
H(p) <= liminf_(q -> p) H(q) <= lim_(q up to p) H(q) <= H(p).
```

With Step 2 this is item 2 of the claim.

**Step 4 (EG0).** For `p < p_c`, sharpness gives `sum_r M_r(p) = chi_p < infinity`.
So `M_r(p)` is bounded, and `g(p) <= 0`. Item 2 then gives
`g(p_c) = lim_(p up to p_c) g(p) <= 0`. Combined with `g(p_c) >= 0`, this is
`g(p_c) = 0`.

**Where the argument is specific.** Step 0 needs the sphere to split into
polynomially many classes (types) on which `tau` is constant. Step 1 needs
concatenating a type with itself to be geodesic and to give the type `Jv`. A
general Cayley graph has neither property.

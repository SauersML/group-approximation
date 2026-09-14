---
rg: 2
id: support-three-zero-divisor-quasimorphism-bound-proof
kind: route
title: Combine the three positive relations with the quasimorphism inequality for the third difference
target: support-three-zero-divisor-differences-bounded-quasimorphism
requires:
  - zero-divisor-support-vertex-cones-contain-positive-relations
---

Let `phi` be homogeneous with defect `D`. Recall `phi(1) = 0`,
`phi(g^-1) = -phi(g)`, and step (2) of
`zero-divisor-quasimorphism-isolated-extremes-proof`: a positive relation
among elements of a set `P` forbids `phi > D` on `P` and forbids `phi < -D` on
`P`. That step uses only the defect inequality, and is repeated here: if
`u_(k-1) ... u_0 = 1` with all `phi(u_i) > D`, then
`0 = phi(1) >= sum phi(u_i) - (k-1)D > D >= 0`.

(1) **Conjugation invariance.** For `g, h in G` and `m >= 1`,
`|phi(h g^m h^-1) - phi(g^m)| <= 2D + |phi(h)| + |phi(h^-1)|`, a bound
independent of `m`. Dividing by `m` and using homogeneity,
`phi(h g h^-1) = phi(g)`.

(2) **Reduction to a left zero divisor on `{1, x, y}`.**
- If `alpha beta = 0`, then `a_0^-1 alpha` is a left zero divisor with support
  `{1, x, y}`, `x = a_0^-1 a_1`, `y = a_0^-1 a_2`. The differences
  `a_i^-1 a_j` are, up to inversion, `x`, `y`, `x^-1 y`.
- If `beta alpha = 0`, then `alpha^* beta^* = 0`, so `alpha^*` is a left zero
  divisor with support `{a_0^-1, a_1^-1, a_2^-1}`. Its left differences are
  `a_i a_j^-1 = a_j (a_j^-1 a_i) a_j^-1`. By (1) they carry the same `phi`
  values as `a_j^-1 a_i`, so the bound for `alpha^*` gives the bound for
  `alpha`.

So assume `supp alpha = {1, x, y}` and `alpha beta = 0`.

(3) **Values.** Put `a = phi(x)`, `b = phi(y)`, `c = phi(x^-1 y)`. The defect
inequality with `phi(x^-1) = -a` gives

```text
b - a - D <= c <= b - a + D.                                   (Q)
```

(4) **Three positive relations.** By consequence 4 of
`zero-divisor-support-vertex-cones-contain-positive-relations`, there are
positive relations among `{x^-1, y^-1}`, among `{x, y^-1 x}`, and among
`{y, x^-1 y}`. Their `phi` values are `(-a, -b)`, `(a, -c)` and `(b, c)`. By the
recalled step, none of the following holds:

```text
(1+) a > D and b > D        (1-) a < -D and b < -D
(2+) a > D and c < -D       (2-) a < -D and c > D
(3+) b > D and c > D        (3-) b < -D and c < -D
```

(5) **Bound on `a`.** If `a > 3D`: not (1+) gives `b <= D`; not (2+) gives
`c >= -D`; but (Q) gives `c <= b - a + D < D - 3D + D = -D`. Contradiction.

(6) **Bound on `b`.** If `b > 3D`: not (1+) gives `a <= D`; not (3+) gives
`c <= D`; but (Q) gives `c >= b - a - D > 3D - D - D = D`. Contradiction.

(7) **Bound on `c`.** If `c > 3D`: not (3+) gives `b <= D`; not (2-) gives
`a >= -D`; but (Q) gives `c <= b - a + D <= D + D + D = 3D`. Contradiction.

(8) **Symmetry.** `-phi` is homogeneous with the same defect, and the list in
(4) is invariant under `(a, b, c) -> (-a, -b, -c)` (it exchanges each `+` case
with its `-` case), while (Q) is preserved. So (5)--(7) applied to `-phi` give
`a, b, c >= -3D`. Hence `|a|, |b|, |c| <= 3D`. Since the differences are `x`,
`y`, `x^-1 y` and their inverses, and `phi` is odd, the claim follows.

(9) **Consequence 1.** A homomorphism `phi: G -> R` is a homogeneous
quasimorphism with `D = 0`, so it vanishes on the differences. An element of
`H_1(G; Z)` killed by every homomorphism to `R` has finite order.

(10) **Consequence 2.** For `a in [G, G]`, Bavard duality (as quoted in the
claim) gives `scl(a) = (1/2) sup |phi(a)|/D(phi)` over homogeneous
quasimorphisms with `D(phi) > 0` modulo homomorphisms. Homomorphisms vanish on
`a in [G,G]`, and by (8) every term is at most `3`, so `scl(a) <= 3/2`.

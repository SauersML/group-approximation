---
rg: 2
id: support-three-quasimorphism-five-thirds-proof
kind: route
title: Count syllables in the three positive relations and solve the resulting sign constraints
target: support-three-zero-divisor-quasimorphism-bound-five-thirds
requires:
  - zero-divisor-support-vertex-cones-contain-positive-relations
---

Let `phi` be homogeneous with defect `D`. Recall `phi(1) = 0`, `phi(g^-1) = -phi(g)`,
`phi(g^m) = m phi(g)`, and by induction on `m`,
`|phi(g_1 ... g_m) - sum_i phi(g_i)| <= (m - 1) D`.

(1) **Syllable lemma.** Suppose `w = u_(k-1) ... u_0 = 1` with `u_i in {p, q}` and both
letters occurring. Every cyclic conjugate of `w` also equals `1`, and since both
letters occur some cyclic conjugate starts with `p` and ends with `q`:

```text
w' = p^(e_1) q^(f_1) p^(e_2) q^(f_2) ... p^(e_s) q^(f_s) = 1,   s >= 1, all e_i, f_i >= 1.
```

This is a product of `2s` elements, so with `i = sum e_i >= s` and `j = sum f_i >= s`,

```text
|i phi(p) + j phi(q)| = |phi(w') - sum phi(blocks)| <= (2s - 1) D.
```

If `phi(p), phi(q) >= 0` and `phi(p) + phi(q) > 2D`, then
`i phi(p) + j phi(q) >= s (phi(p) + phi(q)) > 2sD >= (2s - 1) D`, a contradiction.
Applying this to `-phi` gives the other statement.

(2) **Reduction.** As in step (2) of `support-three-zero-divisor-quasimorphism-bound-proof`:
if `alpha beta = 0`, translate to `supp alpha = {1, x, y}`; if `beta alpha = 0`, pass to
`alpha^*`, whose differences are conjugates of inverses of the differences of `alpha`
and carry the same `phi` values up to sign (homogeneous quasimorphisms are
conjugation invariant). So assume `supp alpha = {1, x, y}`, `alpha beta = 0`. The
differences are `x`, `y`, `x^-1 y` and their inverses.

(3) **Values and constraints.** Put `a = phi(x)`, `b = phi(y)`, `c = phi(x^-1 y)`. The defect
inequality gives

```text
b - a - D <= c <= b - a + D.                                              (Q)
```

By consequence 4 of `zero-divisor-support-vertex-cones-contain-positive-relations`
there are positive relations using both letters among `{x^-1, y^-1}`, `{x, y^-1 x}` and
`{y, x^-1 y}`, with values `(-a, -b)`, `(a, -c)`, `(b, c)`. By (1) none of these holds:

```text
(1+) a >= 0, b >= 0, a + b > 2D        (1-) a <= 0, b <= 0, a + b < -2D
(2+) a >= 0, c <= 0, a - c > 2D        (2-) a <= 0, c >= 0, a - c < -2D
(3+) b >= 0, c >= 0, b + c > 2D        (3-) b <= 0, c <= 0, b + c < -2D
```

(4) **`a <= 5D/3`.** Suppose `a > 5D/3`, so `a > 0`.
- If `b >= 0`: not (1+) gives `b <= 2D - a`. By (Q), `c <= b - a + D <= 3D - 2a < 0`.
  Not (2+) gives `c >= a - 2D`. So `a - 2D <= 3D - 2a`, i.e. `a <= 5D/3`. Contradiction.
- If `b < 0`: by (Q), `c < D - a < 0`. Not (2+) gives `c >= a - 2D`, so `a - 2D < D - a`,
  i.e. `a < 3D/2`. Contradiction.

(5) **`b <= 5D/3`.** Suppose `b > 5D/3`.
- If `a >= 0`: not (1+) gives `a <= 2D - b`. By (Q), `c >= b - a - D >= 2b - 3D > 0`.
  Not (3+) gives `c <= 2D - b`. So `2b - 3D <= 2D - b`, i.e. `b <= 5D/3`. Contradiction.
- If `a < 0`: by (Q), `c > b - D > 0`. Not (3+) gives `c <= 2D - b`, so `b - D < 2D - b`,
  i.e. `b < 3D/2`. Contradiction.

(6) **`c <= 5D/3`.** Suppose `c > 5D/3`.
- If `b >= 0`: not (3+) gives `b <= 2D - c`. By (Q), `a <= b - c + D <= 3D - 2c < 0`.
  Not (2-) gives `a >= c - 2D`. So `c - 2D <= 3D - 2c`, i.e. `c <= 5D/3`. Contradiction.
- If `b < 0`: by (Q), `a < D - c < 0`. Not (2-) gives `a >= c - 2D`, so `c - 2D < D - c`,
  i.e. `c < 3D/2`. Contradiction.

In each case the strict inequalities used hold also when `D = 0`.

(7) **Symmetry.** `-phi` is homogeneous with the same defect, (Q) is invariant under
`(a, b, c) -> (-a, -b, -c)`, and the list in (3) is invariant (each `+` case goes to its
`-` case). So (4)--(6) give `a, b, c >= -5D/3`, hence `|a|, |b|, |c| <= 5D/3`.

(8) **Consequence 1.** For `d in [G, G]`, Bavard duality gives
`scl(d) = (1/2) sup |phi(d)| / D(phi)` over homogeneous quasimorphisms with `D(phi) > 0`;
homomorphisms vanish on `d`. By (7) each term is at most `5/3`, so `scl(d) <= 5/6`.

(9) **Consequence 3.** At `(a, b, c) = (5D/3, D/3, -D/3)`: (Q) holds with equality on the
right; (1+) fails since `a + b = 2D`; (2+) fails since `a - c = 2D`; (3+), (3-) fail since
`b > 0 > c`; (1-), (2-) fail since `a > 0`. So the inequalities of (1) and (Q) alone
cannot improve `5/3`.

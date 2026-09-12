---
rg: 2
id: torsion-free-integral-zeta-euler-product-proof
kind: route
title: Count closed words by rotation orbits, using torsion-freeness to pass from powers of words to their primitive roots
target: torsion-free-integral-zeta-is-an-integer-euler-product
requires: []
---

**Word expansion.** Write `T = sum_x x` over letters `x = (i,j,g)`, each read as
`T_ij(g) E_ij g`. Expanding `T^j` and taking `Tr = sum_i (coefficient of e in
the (i,i) entry)` gives

```text
Tr(T^j) = sum over closed words x_1...x_j of prod_t weight(x_t).
```

A product of matrix units is nonzero exactly when consecutive indices match,
the trace forces the index path to close, and the coefficient of `e` forces
`g_1...g_j = e`.

**Rotation.** Rotation maps closed words to closed words:
- the index path rotates;
- `g_2...g_j g_1 = g_1^(-1)(g_1...g_j) g_1 = e`;
- the weight is unchanged.

**Primitive roots.** Every word `v` of length `j` is `u^(j/d)` for a unique
primitive word `u` of length `d | j`, and its rotation orbit has size `d`.

- If `v` is closed and `j/d >= 2`, the concatenation `uu` is a well-formed
  path, so `u` closes its index path.
- Its product satisfies `(prod u)^(j/d) = e`. Since `G` is torsion-free,
  `prod u = e`. So `u` is closed.
- Conversely, powers of closed words are closed.

Rotation orbits of closed words of length `j` with primitive root of length `d`
therefore correspond bijectively to necklaces `c` of length `d`. Each such orbit
has `d` elements of weight `w(c)^(j/d)`, which gives

```text
Tr(T^j) = sum_(d | j) d * sum_(|c| = d) w(c)^(j/d).
```

Only finitely many necklaces have each length, so every sum is finite.

**Euler product.**

```text
log prod_c (1 - w(c) z^|c|)^(-1)
    = sum_c sum_(r >= 1) w(c)^r z^(|c| r) / r
    = sum_j (z^j / j) sum_(d | j) d sum_(|c| = d) w(c)^(j/d)
    = sum_j Tr(T^j) z^j / j.
```

In the middle step `j = |c| r`, `d = |c|` and `1/r = d/j`. Each factor lies in
`1 + z Z[[z]]`, and only finitely many factors affect each coefficient, so the
product has integer coefficients.

**Frobenius congruence.** In `Tr(T^(pj))`:
- the terms with `d | j` are `d (w^(j/d))^p == d w^(j/d) (mod p)` by Fermat,
  and these are exactly the terms of `Tr(T^j)`;
- a divisor `d` of `pj` that does not divide `j` has
  `v_p(d) = v_p(j) + 1 >= 1`, so its terms vanish mod `p`.

**FK form.** For self-adjoint `T` and real `|z| < 1/||T||`, the operator
`1 - zT` is positive invertible. Hence
`log det_N(G)(1 - zT) = Tr log(1 - zT) = -sum_j Tr(T^j) z^j / j`.

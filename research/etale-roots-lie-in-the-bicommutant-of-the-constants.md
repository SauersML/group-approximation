---
rg: 2
id: etale-roots-lie-in-the-bicommutant-of-the-constants
kind: claim
title: An etale root of a nonsingular matrix equation commutes with every matrix commuting with the constants, so amplification never creates etale roots and some semisimple tuples have no etale root at any amplification
distinct_from:
  etale-roots-of-the-semisimplification-lift-to-exact-roots: that lifts etale roots of the semisimplification to exact roots and leaves open whether every semisimple tuple has an etale root after amplification; this shows amplification is inert for etale roots and answers that question negatively.
  amplified-algebraic-roots-in-characteristic-zero: that is the approximate root premise for every tuple; this only limits the etale-degeneration route to it and decides nothing about exact non-etale or approximate roots.
  congruence-constants-have-exact-nonsingular-roots: that produces exact roots for p-adically congruence tuples; this is a rigidity statement about which roots can be etale.
artifacts:
  - research/artifacts/hl-kl-etale-g1-2026-09-14.md
---

**ESTABLISHED** through `etale-roots-lie-in-the-bicommutant-of-the-constants-proof`
(first-order substitution over the dual numbers and linear algebra; unreviewed,
no novelty claimed).

**Setup.** `L` is any field, `c = (c_1, ..., c_k)` is in `GL_N(L)^k`, and
`w = y_1 ... y_l` in `F_k * <x>` has exponent sum `m` in `x`. As in
`etale-roots-of-the-semisimplification-lift-to-exact-roots`:
- `S_i` is the value of `y_{i+1} ... y_l` at `(T ; c)`;
- `D_{T,c}(Y) = sum over y_i = x of S_i^{-1} Y S_i - sum over y_i = x^{-1} of S_{i-1}^{-1} Y S_{i-1}`;
- a root `T` of `w(T ; c) = 1` is *etale* if `D_{T,c}` is invertible.

Write `C(c) = { X in M_N(L) : X c_j = c_j X for all j }` for the commutant of the
constants.

**Theorem G (bicommutant).** Every etale root `T` commutes with every `X` in
`C(c)`. So `T` lies in the commutant of `C(c)`, the bicommutant of the
constants.

**Corollary H (amplification is inert).** For every `r >= 1`, the etale roots of
`w(T ; c (x) 1_r) = 1` in `GL_{Nr}(L)` are exactly the matrices `T_0 (x) 1_r`
with `T_0` an etale root of `w(T_0 ; c) = 1` in `GL_N(L)`. So the hypothesis
"for some `r >= 1`" in Corollary F of
`etale-roots-of-the-semisimplification-lift-to-exact-roots` is equivalent to
`r = 1`.

**Corollary I (commuting semisimple tuples).** Let `d = (d_1, ..., d_k)` be
diagonal, let `f_j` be the exponent sum of the letter `d_j` in `w`, and call
indices `p, q` equivalent if `d_{j,pp} = d_{j,qq}` for every `j`. Suppose `m != 0`
in `L`.
- An etale root is diagonal and constant on equivalence classes.
- Such a diagonal `T = diag(t_1, ..., t_N)` is a root if and only if
  `t_p^m prod_j d_{j,pp}^{f_j} = 1` for every `p`.
- It is etale if and only if `s_pq(T) != 0` for all inequivalent `p, q`, where
  `s_pq` is the number of Example 2 of the etale node:
  `s_pq = sum over y_i = x of psi_pq(S_i) - sum over y_i = x^{-1} of psi_pq(S_{i-1})`,
  with `psi_pq(S) = S_qq / S_pp`.

So for commuting semisimple constants, existence of an etale root at any
amplification is a finite check over the choices of `m`-th roots.

**Corollary J (a semisimple tuple with no etale root).** Let `char L != 2`,
`a = diag(2, 1)`, `b = 1` and `w = x^2 a x^{-1} a^{-1} b`, with `m = 1`.
- For no `r >= 1` does `w(T ; a (x) 1_r, b (x) 1_r) = 1` have an etale root.
- Over a field of characteristic `0`, the roots at `r = 1` are exactly
  `T = 1 + t E_12` for `t` in `L`, and each has `D_{T,(a,b)}(E_12) = 0`.

This is the semisimplification, along the full flag, of the caution tuple
`(diag(2, 1), 1 + E_12)` of the etale node.

**Remark (etaleness is lost under degeneration).** The caution tuple itself has
an etale root: at `T_0 = [[5/2, -4/3], [9/2, -2]]` the operator `D_{T_0,(a, 1+E_12)}`
has matrix (columns `D(E_11), D(E_12), D(E_21), D(E_22)`, coordinates
`E_11, E_12, E_21, E_22`)

```text
[   -5    -171/16    10/3     6   ]
[  10/3    99/16      -2    -10/3 ]
[   -9   -243/16      6       9   ]
[    6    171/16    -10/3    -5   ]
```

with determinant `9/4` (exact rational arithmetic, script in the artifact). So a
tuple can have etale roots while its semisimplification has none at any
amplification.

**Consequences.**
- The gap sentence of `etale-roots-of-the-semisimplification-lift-to-exact-roots`
  ("does every semisimple tuple have an etale root after amplification?") has
  answer **no**, even over `Q` with a single non-unitarizable constant.
- Corollary F with any invariant flag and any `r` certifies a tuple only if some
  block-diagonal part has an etale root at `r = 1`. For the pair of Corollary J,
  every invariant flag gives the tuple itself, so the method never applies; yet
  `T = 1` is an exact root, so this is not a counterexample to
  `amplified-algebraic-roots-in-characteristic-zero`.
- Any proof of that premise for all tuples must therefore handle roots that are
  not etale (for example the clean roots `1 + t E_12`, `t != 0`, whose kernel is
  exactly the tangent line of the centralizer orbit) or produce approximate
  roots without an exact etale model.

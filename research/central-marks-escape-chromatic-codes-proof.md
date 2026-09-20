---
rg: 2
id: central-marks-escape-chromatic-codes-proof
kind: route
title: Cayley-graph colouring and translation-number proof that central marks escape chromatic codes
target: central-marks-escape-chromatic-codes
requires: []
---

Self-contained.  No literature is used.  The Maruyama sentence quoted in
`lifted-thompson-t-perfect-centre-cubically-elliptic` gives the sharp defect;
here the crude defect `2` is proved directly.

## 0. Exactness

A word of finite relator area is trivial in `Gamma`.  So any data meeting CCC1
or CDC2 satisfies the displayed equations exactly in `Gamma`.  Everything
below is an obstruction to those exact equations.  It therefore holds for
every presentation and every area bound.

## 1. CDC needs an infinite conjugacy class

Let `C` be the conjugacy class of the mark `x != 1`, and suppose `C` is finite.
CDC2 gives `b_w = b_v c` for some `c in C`, for every oriented edge `(v,w)`.
Since `1` is not in `C`, we have `b_v != b_w`.  So `v |-> b_v` is a graph
homomorphism from `Lambda` into the loopless Cayley graph
`K = Cay(Gamma, C u C^(-1))`, and every vertex of `K` has degree at most `2|C|`.

Well-order the vertices of `K` and colour them greedily.  Each vertex has at
most `2|C|` neighbours, so a colour from `{1, ..., 2|C|+1}` unused by earlier
neighbours always exists.  Hence

```text
chi(K) <= 2|C|+1,   chi(Lambda) <= chi(K).
```

This contradicts `chi(Lambda) = infinity`.

For central `x` we have `C = {x}`, and `K` is a disjoint union of paths and
cycles, so `chi <= 3`.  If CDC2 holds for both orientations of an edge `vw`,
then

```text
x = b_v^(-1) b_w = (b_w^(-1) b_v)^(-1) = x^(-1),
```

so `x^2 = 1`.

## 2. Translation number on T̄

Every `h in T̄` commutes with `z` and is increasing.  So the displacement
`d_h(x) = h(x) - x` is `1`-periodic.

**Oscillation.**  For `x <= y < x+1`,

```text
d_h(y) <= h(x+1) - x = d_h(x) + 1,
```

and symmetrically.  Hence `M(h) - m(h) <= 1`, where `m(h)` and `M(h)` are the
infimum and supremum of `d_h`.

**Existence.**  Let `a_n = h^n(0)`.  Then `a_(p+q) = h^p(a_q)`, and the
oscillation bound applied to `h^p` gives

```text
|a_(p+q) - a_p - a_q| <= 1.
```

So `tau(h) = lim a_n / n` exists and is finite (Fekete, applied to `a_n + 1`
and to `-a_n + 1`).  Since `a_n` is a sum of `n` values of `d_h`, `tau(h)`
lies in `[m(h), M(h)]`.

**Properties.**

- (P1) `tau(h^n) = n tau(h)`.
- (P2) `tau(z^m h) = m + tau(h)`, since `(z^m h)^n(0) = h^n(0) + mn`.
- (P3) `tau(k h k^(-1)) = tau(h)`.  Indeed `(k h k^(-1))^n(0) = k(h^n(k^(-1)(0)))`.
  Moving the argument by the bounded amount `|k^(-1)(0)|`, and then applying
  `k`, changes the value by at most a constant `c(k)` independent of `n`.
  This uses the oscillation bound applied to `h^n` and to `k`.
- (P4) For a commutator `q = f g f^(-1) g^(-1)`, write `d_q(x)` as the sum of
  the displacements of `g^(-1)`, `f^(-1)`, `g` and `f` at successive points.
  Since `m(f^(-1)) = -M(f)`, the `f` and `f^(-1)` terms together lie in
  `[-1, 1]`, and likewise for `g`.  So `|d_q| <= 2`, and by existence
  `|tau(q)| <= 2`.

## 3. The lemma

Suppose `[F,G] = z^m`, that is, `FG = z^m GF`.  Since `GF = F^(-1)(FG)F`,
properties (P3) and (P2) give

```text
tau(FG) = tau(z^m GF) = m + tau(GF) = m + tau(FG),
```

so `m = 0`.  The same computation proves the general form for any homogeneous
quasimorphism `phi` with `phi(z) != 0`.  Such a `phi` is conjugation
invariant and additive on commuting pairs, which gives the analogues of (P3)
and (P2).

## 4. CCC

CCC1 with mark `z^k` reads `[c_v, h_v] = a_v z^k a_v^(-1) = z^k`.  By §3 this
forces `k = 0`.

## 5. Exact T-tables lift

Let `p : T̄ -> T` be the quotient map, with kernel `<z>`.

**Commuting pairs lift.**  For `f, g in T` with lifts `F, G`, the commutator
`[F,G]` does not depend on the choice of lifts, because the ambiguity is
central.  If `[f,g] = 1`, then `[F,G]` lies in `<z>`, and by §3 it equals `1`.

**Tables lift.**  Take an exact table in `T`:

```text
[c_v, h_v] = a_v y a_v^(-1),   [c_w, h_v] = 1,
```

and choose lifts `c̃_v, h̃_v, ã_v, ỹ`.  Off the diagonal, `[c̃_w, h̃_v] = 1`
by the previous paragraph.  On the diagonal,

```text
[c̃_v, h̃_v] = ã_v (ỹ z^(e_v)) ã_v^(-1)
```

for some integer `e_v`.  By (P3), (P2) and (P4),
`|tau(ỹ) + e_v| = |tau([c̃_v, h̃_v])| <= 2`.  So `e_v` takes at most five
values.

Since `chi(Lambda)` is at most the sum of the chromatic numbers of the induced
subgraphs `Lambda_e = {v : e_v = e}`, some `Lambda_e` has infinite chromatic
number.  On it the lifted data form an exact table with the single mark
`ỹ z^e`.

What does not transfer is the area.  A lifted word may represent the right
element only after long central corrections.

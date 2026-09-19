---
rg: 2
id: bounded-area-conjugacy-difference-code-kills-mf-mark
kind: claim
title: A bounded-area high-chromatic conjugacy-difference code kills its MF mark
distinct_from:
  infinite-chromatic-commutator-code-kills-mf-mark: that compares diagonal marked commutators with off-diagonal commuting pairs; this uses one vertex word per color and makes every edge difference a conjugate of the marked word.
  bounded-area-high-chromatic-conjugacy-collapse: that uses normalized-Hilbert--Schmidt Carmichael relations among conjugates of an order-three vertex; this is an operator-norm criterion for arbitrary vertex words and one conjugacy-difference mark.
artifacts:
  - research/bounded-area-conjugacy-difference-code-proof.md
---

Let `Gamma=<S|R>` be finitely presented and let `z` be a word.  Suppose a
graph `Lambda=(V,E)` has infinite chromatic number and there are free words

```text
b_v                         (v in V),
a_(v,w)                     (vw in E)                  (CDC1)
```

and one constant `A` such that every oriented edge satisfies

```text
Area_R(b_v^(-1)b_w a_(v,w) z^(-1) a_(v,w)^(-1))<=A.   (CDC2)
```

Then

```text
z in Rad_MF(Gamma).                                    (CDC3)
```

No trace, density, torsion hypothesis, stability theorem, Property T, or
literature input occurs.  The vertex and conjugator words may have unbounded
length; only the area in `(CDC2)` is uniform.

The result is tailored to norm-matrix coronas.  In one fixed matrix
coordinate, compactness gives a finite operator-norm palette for the vertex
unitaries.  Infinite chromatic number forces an edge whose endpoint
evaluations are arbitrarily close.  Uniform area then identifies their
difference with a conjugate of `z` at a cost independent of which edge the
coordinate selected.

DERIVATION
bounded-area-conjugacy-difference-code-proof

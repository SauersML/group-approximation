---
rg: 2
id: stw95-order-reflection-localizes-perforation-proof
kind: route
title: Localize a concrete perforation inequality to two external-image elements
target: stw95-order-embedded-inner-cofinal-cu-image-forces-pure-product
requires:
  - stw95-inner-cofinal-cu-image-gives-almost-divisibility
---

Purity of `A` and `B` says that their Cuntz semigroups absorb `Cu(Z)`.
Associativity of the Cu tensor product therefore shows that

```text
S=Cu(A) tensor_Cu Cu(B)
```

is pure, hence both almost divisible and almost unperforated.  Hypothesis
`(IC)` and `stw95-inner-cofinal-cu-image-gives-almost-divisibility` already
give almost divisibility of `T`.  It remains to prove almost
unperforation.

Suppose

```text
(n+1)x <= n y                                             (P1)
```

in `T`, where `n>=1`, and fix `x_0<<x`.  Apply `(IC)` to choose
`a_0<<a` in `S` with

```text
x_0<=theta(a_0),             theta(a)<=x.                (P2)
```

Because a Cu-morphism preserves compact containment and addition respects
compact containment,

```text
(n+1)theta(a_0) << (n+1)theta(a)
                  <= (n+1)x <= n y.                      (P3)
```

Choose a rapidly increasing sequence `(y_j)` with supremum `y`.  The Cu
axioms give `n y=sup_j n y_j`.  From `(P3)` there is an index `j` such that

```text
(n+1)theta(a_0) <= n y_j,            y_j<<y.             (P4)
```

Apply `(IC)` once more, now to `y_j<<y`.  There are `b_0<<b` in `S` with

```text
y_j<=theta(b_0),              theta(b)<=y.                (P5)
```

Equations `(P4)` and `(P5)` imply

```text
theta((n+1)a_0) <= theta(n b_0).
```

Order reflection of `theta` gives `(n+1)a_0<=n b_0`.  Almost
unperforation of `S` gives `a_0<=b_0`.  Returning through `theta` and using
`(P2)` and `(P5)` yields

```text
x_0<=theta(a_0)<=theta(b_0)<=theta(b)<=y.                (P6)
```

Every element of a Cu-semigroup is the supremum of a rapidly increasing
sequence.  Since `(P6)` holds for every `x_0<<x`, it follows that `x<=y`.
Thus `T` is almost unperforated.  Together with the already proved almost
divisibility, this makes `T` pure and hence makes `A tensor_min B` pure.

At no point is an arbitrary element of `T` lifted to `S`.  Only the two
way-below windows in `(P2)` and `(P5)` are bracketed by image elements, so
the proof neither assumes nor derives surjectivity of `theta`.

---
rg: 2
id: stw95-order-reflection-localizes-perforation-proof
kind: route
title: Diagonalize inner image brackets into a global Cu inverse
target: stw95-order-embedded-inner-cofinal-cu-image-forces-pure-product
requires:
  - stw95-inner-cofinal-cu-image-gives-almost-divisibility
---

We first prove the abstract assertion.  Fix `x in T` and choose a rapidly
increasing sequence

```text
x_1<<x_2<<... ,             sup_n x_n=x.               (P1)
```

Apply `(IC)` to `x_1<<x` to obtain `b_1<<c_1` with

```text
x_1<=theta(b_1)<<theta(c_1)<=x.                         (P2)
```

Suppose the pair at stage `n-1` has been chosen.  Both `x_n` and
`theta(b_(n-1))` are way below `x`; for the latter this follows from
`theta(b_(n-1))<<theta(c_(n-1))<=x`.  Axiom `(O2)` supplies `z_n<<x`
dominating both (equivalently, take a sufficiently late term of a rapidly
increasing approximation to `x`).  Apply `(IC)` to `z_n<<x` and obtain

```text
x_n, theta(b_(n-1)) <= z_n <= theta(b_n)
                      << theta(c_n) <= x.               (P3)
```

Order reflection turns the middle comparison into
`b_(n-1)<=b_n`.  Hence `b=sup_n b_n` exists, and preservation of increasing
suprema gives

```text
x=sup_n x_n <= theta(b)=sup_n theta(b_n) <= x.           (P4)
```

Thus every `x in T` is in the image.  An order-embedding Cu-morphism which
is surjective is a Cu-isomorphism: its inverse preserves order, addition,
zero, and increasing suprema, and therefore also the way-below relation.

Conversely, if `theta` is a Cu-isomorphism and `x'<<x`, take
`a'=theta^(-1)(x')` and `a=theta^(-1)(x)`.  Then `a'<<a` and `(IC)` holds
with equality at both ends.

For the C-star application, purity of `A` and `B` makes
`S=Cu(A) tensor_Cu Cu(B)` pure by `Cu(Z)`-absorption.  The isomorphism carries
almost divisibility and almost unperforation to `T`, so `A tensor_min B` is
pure.  The earlier perforation-localization proof was valid but unnecessarily
weak: the same hypotheses already force the global lift `(P4)`.

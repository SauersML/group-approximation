---
rg: 2
id: crossed-fox-lamp-parity-table-area-proof
kind: route
title: Pair the identity and involution table cells under the p-lamp Fox cocycle
target: thompson-clifford-table-area-grows-linearly-in-rank
requires:
  - thompson-clifford-central-product-tape
---

The central extension `(TCP2)` has quotient

```text
(directSum_X F_2^2) semidirect V.
```

Projection to the first lamp coordinate is a crossed `V`-cocycle.  After
choosing integral lifts on the finite generating set, the free-group crossed
derivative `D` reduces to this cocycle modulo two.  Hence every defining
relator has even derivative coefficients, although its integral derivative
need not vanish.  In a generator-adapted presentation the involution relator
contributes `D(p^2)=2e_xi`.  In an arbitrary presentation the square of a
word representing `p_xi` instead has derivative `2D(w_p)`, still nonzero;
the area estimate below then forces some defining relator to have nonzero
derivative, so `C_P>0`.

If a null word is a product of `A` conjugates of defining relators or their
inverses, then each relator has trivial actor image and

```text
D(t r^(+-1) t^(-1))=pi(t)D(r^(+-1)).
```

Actor translation preserves the coefficient `ell^1` norm, while
`D(r^(-1))=-D(r)`.  Therefore `||D(z)||_1<=A C_P`, proving the area bound for
arbitrary van Kampen expressions, not merely for preferred diagrams.

For the product `a` of `N` distinct `p`-lamps, every representative `u` has
`D(u) mod 2` equal to the indicator of those sites, so `||D(u)||_1>=N`.
An arbitrary identity representative `v` cannot cancel this lower bound in
all table cells: the `(1,1)` and `(a,a)` derivatives are `D(v)` and
`2D(u)-D(v)`, and their norms have sum at least `2||D(u)||_1`.  Applying the
area estimate to the larger one proves the claimed `N/C_P` lower bound.

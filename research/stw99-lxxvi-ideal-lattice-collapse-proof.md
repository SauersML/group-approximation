---
rg: 2
id: stw99-lxxvi-ideal-lattice-collapse-proof
kind: route
title: Identify both Cuntz semigroups with their ideal lattices
target: stw99-lxxvi-strong-pure-infiniteness-implies-cu-regularity
requires:
  - stw99-lxxvi-first-factor-map-has-identical-coarse-shadows
artifacts:
  - research/artifacts/stw99-lxxvi-strong-pure-infiniteness-audit-2026-08-30.md
---

First consider the more general statement.  Suppose that `A` and
`A tensor_min Z` are separable purely infinite C\*-algebras in the
Kirchberg--Rordam sense.  For a separable purely infinite algebra `C`, the
map (with positive representatives taken in `C tensor K`)

```text
Lambda_C:Cu(C) -> Lat(C),       [c] |-> Ideal_C(c)            (1)
```

is an order isomorphism onto the lattice of closed two-sided ideals.  Indeed,
pure infiniteness, which is stable under tensoring with `K`, says precisely
that

```text
c Cuntz-subequivalent to d    iff    c belongs to Ideal_C(d).
```

Surjectivity in (1) follows because every ideal of a separable C\*-algebra is
sigma-unital and hence has a strictly positive element.  Here the ideal of a
stabilized positive element is transported back along the standard
`Lat(C tensor K)~=Lat(C)` correspondence.  Under (1), addition is ideal join
and every element is idempotent.

The square

```text
Cu(A) ----------------Cu(iota_A)---------------> Cu(A tensor Z)
 |                                                   |
Lambda_A                                      Lambda_(A tensor Z)
 |                                                   |
 v                                                   v
Lat(A) ---------------- I |-> I tensor Z ----------> Lat(A tensor Z)
```

commutes.  On a positive representative this is the identity

```text
Ideal_(A tensor Z)(a tensor 1_Z)=Ideal_A(a) tensor Z.        (2)
```

The bottom arrow is an isomorphism by the slice-map theorem for the simple
nuclear algebra `Z`, as recorded in
`stw99-lxxvi-first-factor-map-has-identical-coarse-shadows`.  The two
vertical arrows are isomorphisms by pure infiniteness.  Therefore the top
arrow `Cu(iota_A)` is an isomorphism.  This proves the general criterion.

Now let `A` be separable and strongly purely infinite.  Strong pure
infiniteness implies pure infiniteness.  Kirchberg--Sierakowski's tensor
product theorem in
[*Filling families and strong pure infiniteness*](https://arxiv.org/abs/1503.08519)
shows that the minimal tensor product of a strongly purely infinite algebra
with an exact algebra is strongly purely infinite.  Since `Z` is nuclear and
hence exact, `A tensor_min Z` is strongly purely infinite, and the criterion
above applies.

Finally, `A` really is pure in the sense of Problem LXXVI.  Its Cuntz
semigroup is the idempotent ideal lattice.  Almost unperforation is immediate:
if `(k+1)x<=ky`, idempotence reduces this to `x<=y`.  Almost divisibility is
also immediate: for `x'<<x` and `k>=1`, take `y=x`; then

```text
x'<=k y=x<=(k+1)y.
```

Thus strong pure infiniteness supplies both the hypothesis and the claimed
Cu-regularity conclusion of Problem LXXVI.

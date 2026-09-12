---
rg: 2
id: two-field-centralizer-fiber-closure-proof
kind: route
title: Close the two sampled centralizer fibers under parallel sum and Hua multiplication
target: two-untwisted-field-matchings-force-complete-cross-commutation
requires: []
---

Define

```text
S={r in F : [X(rt),Z(t)]=1 for every t in F}.                 (CFC1)
```

The identity element gives `0 in S`, while the two sampled families give
`1,alpha in S`.  Centralizers are subgroups and `X` is additive, so

```text
r,s in S  ==>  r+s in S.                                     (CFC2)
```

There is a second closure operation which uses the `Z` fiber.  If `r,s` are
nonzero and distinct, then for every `a`, the two elements

```text
Z(r^(-1)a),                  Z(s^(-1)a)
```

commute with `X(a)`.  Their product does too.  On putting
`t=(r^(-1)+s^(-1))a`, this says

```text
h(r,s):=(r^(-1)+s^(-1))^(-1)=rs/(r+s) in S.                  (CFC3)
```

These two elementary fiber closures already make `S` a field.  Indeed, if
`u in S\{0,1}`, apply `(CFC3)` to `u+1` and `1` and then `(CFC2)`:

```text
h(u+1,1)+1=(u+1)/u+1=u^(-1) in S.                            (CFC4)
```

The cases `u=1` and `u=0` are harmless, so `S` is inverse-closed away from
zero.  Hua's identity in characteristic two is

```text
a^2 b
 = a + (a^(-1) + (b^(-1)+a)^(-1))^(-1),                     (CFC5)
```

when `a,b` are nonzero and `ab!=1`; when `ab=1`, the left side is just `a`.
Thus `a^2 b in S` for all `a,b in S`.  Taking `b=1` shows that Frobenius
squaring maps the finite additive group `S` into itself.  It is injective,
hence surjective.  Given `c,b in S`, choose `a in S` with `a^2=c`; `(CFC5)`
then gives `cb in S`, including its exceptional case.  Therefore `S` is a
subfield.  Since it contains `alpha` and `F_2(alpha)=F`, it equals `F`, which
is `(UFM2)`.

For the quantitative statement use the commuting defect `d` and `D` from
the target.  Product expansion, unitary invariance, and Minkowski give

```text
D(r+s) <= D(r)+D(s),
D(h(r,s)) <= D(r)+D(s).                                      (CFC6)
```

Assign weight one to `1` and `alpha`, and assign to the output of either
operation the sum of the input weights.  Then `(CFC6)` proves `(UFM4)`.
The inverse construction `(CFC4)` increases weight by at most three.  Reading
Hua's identity as a circuit therefore gives

```text
kappa(a^2 b) <= 3 kappa(a)+kappa(b)+12.                       (CFC7)
```

unless `ab=1`, when no increase is needed.  Build `alpha^k` recursively as
`(alpha^i)^2` for `k=2i` and as `(alpha^i)^2 alpha` for `k=2i+1`.  If `C_k`
is its weight, then

```text
C_0=C_1=1,                  C_k <= 3 C_(floor(k/2))+13,
C_k < 8 3^(ceil(log_2 k))       for k>=1.                    (CFC8)
```

Every field element is a sum of at most `n` of
`1,alpha,...,alpha^(n-1)`, proving `(UFM5)` and `(UFM6)`.  Replacing one
unitary in a commuting defect changes it by at most twice the normalized-HS
distance.  Apply this before and after `(UFM6)`, use that multiplication by
`alpha` preserves the uniform measure, and Minkowski gives `(UFM8)`.

For the twisted consequence, take canonical Weyl operators `P,Q` on
`ell^2(F)` with

```text
P(a)Q(b)=(-1)^beta(a,b)Q(b)P(a).                              (CFC9)
```

The additive tables `X(a)=U(a) tensor P(a)` and
`Z(b)=W(b) tensor Q(b)` satisfy `(UFM1)`, because each sampled sign occurs
twice.  Complete cross-commutation of `X,Z` is exactly `(UFM10)`.  Finally,
conjugation by the `W(b)` translates the character atoms of `U` freely and
transitively through the `2^n` characters, so all atom ranks agree and
`2^n` divides the ambient dimension.

---
rg: 2
id: digit-shear-internal-no-go-proof
kind: route
title: Quotient to two free factors and exclude the Fourier intertwiner
target: digit-shear-has-no-internal-maximal-conjugator
requires: []
---

Kill `x,b_1,...,b_s` in `Gamma'`. Every defining relation then becomes

```text
[a_i,t]=[a_i,d]=1,
```

and there are no further relations among `t,d` or among the `a_i`. Hence
there is a quotient

```text
q : Gamma' -> F(t,d) x F(a_1,...,a_s).
```

Suppose that the unitary `V` in the claim existed. Apply the induced map on
maximal group C-star algebras and then the left regular representation of the
quotient. Its image `U` is a unitary in

```text
L(F(t,d)) bar_tensor L(F(a_1,...,a_s))
```

which commutes with the second tensor factor. Since `s>=2`, the second free
group is ICC and its group von Neumann algebra is a factor. Therefore

```text
U in L(F(t,d)) bar_tensor C.
```

It remains to show that there is not even a nonzero `U in L(F(t,d))` with

```text
U lambda(t) = lambda(td) U.                              (1)
```

Write `U=sum_g c_g lambda(g)` in `L^2(F(t,d))`. Comparing Fourier
coefficients in `(1)` gives

```text
c_g = c_((td)^(-1) g t)                                  (2)
```

for every `g`. The `k`-th iterate of the indexing bijection in `(2)` is

```text
g |-> (td)^(-k) g t^k.
```

A finite orbit would therefore give, for some `k>=1`,

```text
g t^k g^(-1) = (td)^k.                                   (3)
```

But `t^k` and `(td)^k` are cyclically reduced words in the free group of
cyclic lengths `k` and `2k`; conjugate cyclically reduced words have equal
cyclic length. Thus `(3)` is impossible, every orbit in `(2)` is infinite,
and square summability forces every orbit-constant coefficient `c_g` to be
zero. Hence `U=0`, contradicting unitarity. This proves the claim.

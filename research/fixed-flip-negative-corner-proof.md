---
rg: 2
id: fixed-flip-negative-corner-proof
kind: route
title: Exactify the central flip and compare signed HS distance with Hamming distance
target: fixed-flip-negative-corner-is-sofic
requires: []
---

Let `p in Sym(Omega)` and let `j` be a fixed-point-free involution. The set

```text
G={z:p j z=j p z}
```

is `j`-invariant. On `G`, the permutation `p` maps `j`-pairs injectively to
`j`-pairs and respects their two sheets. Complete this partial bijection of
`j`-pairs arbitrarily on the complement to obtain `q in C_Sym(Omega)(j)`.
Then

```text
d_H(p,q) <= d_H([p,j],1).                                (FNP1)
```

Apply this separately to the finitely many generators. Fixed relator defects
change by at most the sum of the generator-edit distances along the relator,
so they still vanish. Thus all corrected coordinates commute exactly with
`j_n`.

Choose one vector from each two-point `j_n`-orbit. The vectors

```text
e_z-e_(j_n z)
```

form a basis of `V_n^-`. Every permutation centralizing `j_n` permutes these
basis lines and may reverse their signs. Its restriction is therefore an
element of the hyperoctahedral group `B_d=C_2 wr Sym(d)`.

For `U in B_d`, let `a` be the number of positive fixed basis vectors and
`b` the number of negative fixed basis vectors. With normalized trace on
`M_d`,

```text
||U-I||_2^2/2 = 1-a/d+b/d.                               (FNP2)
```

Embed `B_d` into `Sym({1,...,d} times {+,-})` in the standard way. Its
normalized Hamming distance from the identity is

```text
d_H(U_tilde,1)=1-a/d.                                    (FNP3)
```

Since `b<=d-a`, `(FNP2)--(FNP3)` give

```text
d_H(U_tilde,1)
 <= ||U-I||_2^2/2
 <= 2 d_H(U_tilde,1).                                   (FNP4)
```

Apply `(FNP4)` to `UV^(-1)`. Vanishing multiplication defects and nonzero
separation are preserved in both directions, so `(FNC4)` embeds its image in
a metric ultraproduct of finite symmetric groups. That image, and hence the
quotient `(FNC5)`, is sofic.

---
rg: 2
id: tensor-isometry-is-an-exact-bipartite-hecke-absorber-proof
kind: route
title: Put the entire spectral gap in one factor and the head in multiplicity
target: rectangular-safe-covariance-has-a-positive-head-absorber
requires:
  - two-raw-roots-have-a-uniform-full-carrier-gap
  - two-raw-unweighted-covariance-kills-jacobson-head
---

Write `alpha=m/(n+m)` with positive integers `m,n`. Let

```text
H_S=V tensor C^n,
H_T=V tensor C^(n+m),

pi_S(g)=beta(g) tensor I_n,
pi_T(g)=beta(g) tensor I_(n+m).
```

Choose the coordinate inclusion `j:C^n->C^(n+m)` and set

```text
S=I_V tensor j,             T=S^*,
Q=I_(H_T)-SS^*.                                        (TIH1)
```

Since `j^*j=I_n`, direct multiplication gives

```text
TS=I_(H_S),                  ST=I_(H_T)-Q.
```

The range of `S` is orthogonal to the range of `Q`, proving `QS=0`;
taking adjoints gives `TQ=0`. This is `(RSC1)--(RSC2)`.

All group action occurs in the first tensor factor, while `S` acts in the
second. Hence

```text
(pi_T(g))S
 =(beta(g) tensor I_(n+m))(I_V tensor j)
 =(I_V tensor j)(beta(g) tensor I_n)
 =S(pi_S(g)),
```

which proves `(RSC3)` for the whole group `F`, not merely for a Kazhdan
set. In particular every displacement on the right side of `(TRG4)` is
zero.

The cokernel dimension is `dim(V)m` and
`dim(H_T)=dim(V)(n+m)`, so `(RSC4)` holds. Finally
`H_Q-I=-2Q`, and the normalized target-corner trace gives

```text
||H_Q-I||_2^2
 =4 tr_(H_T)(Q)
 =4m/(n+m)
 =4alpha.
```

This proves `(RSC5)`.

The construction embeds into one ordinary matrix algebra by passing to
`H_T directSum H_S` and viewing `S` as the corresponding off-diagonal
partial isometry. It is therefore an honest finite-dimensional absorber,
not a formal mismatch of categories.

Property T distinguishes representation types but is blind to extra
multiplicity in the target. Here the source and target carry exactly the
same type `beta` and differ only by `m` copies. Squaring the occurrence
would have to certify equality of those multiplicities. The one-sided
relations deliberately do not do so, which is why the head survives.

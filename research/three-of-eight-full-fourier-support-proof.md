---
rg: 2
id: three-of-eight-full-fourier-support-proof
kind: route
title: Use odd Fourier coefficients to recover the whole context subgroup
target: three-of-eight-transport-forces-chart-conjugacy
requires:
  - heisenberg-subgroup-cuts-are-affine-stabilizer-flats
---

Expanding `(TET2)`, the coefficient of `a in A_1` in `P_(1,S)` is

```text
c_S(a)=|A_1|^(-1) sum_(chi in S) chi(a).                (TEP1)
```

Each summand is `+1` or `-1`.  Since `|S|=3` is odd, their sum is one of
`{-3,-1,1,3}` and in particular never vanishes.  Hence

```text
supp(P_(1,S))=A_1.                                     (TEP2)
```

The same argument gives `supp(P_(2,T))=A_2`.  Conjugation permutes the
canonical basis of `C[Gamma]`, so the support of the left side of `(TET3)`
is `gA_1g^(-1)`.  Linear independence of distinct group elements and `(TEP2)`
therefore prove `(TET4)`.  Notice that this step uses neither a finite
overgroup nor a residual-finiteness hypothesis.

Write `theta(a)=gag^(-1)`.  It is an isomorphism `A_1 -> A_2` fixing the
central mark `J`.  Its contragredient map

```text
theta_*(chi)=chi composed with theta^(-1)               (TEP3)
```

is therefore an affine bijection `X_1 -> X_2`.  Direct substitution in the
character averages gives

```text
g e_(1,chi) g^(-1)=e_(2,theta_*(chi)).                  (TEP4)
```

Thus the left side of `(TET3)` is the sum of the mutually orthogonal atoms
indexed by `theta_*(S)`.  Uniqueness of the character Fourier expansion (or
orthogonality of the minimal projections) gives `T=theta_*(S)` and proves
`(TET5)`.

For sharpness, translate a three-element subset so that it contains `0`.
Its two remaining points are distinct nonzero vectors and hence linearly
independent over `F_2`.  Given two such subsets, an invertible linear map can
send the ordered independent pair of the first to that of the second;
restoring the translations gives an affine bijection.  Conjugating the
generators of `A_1` to the corresponding marked products in `A_2` then
transports all character atoms as in `(TEP4)`, and in particular transports
the prescribed three-atom sum.

---
rg: 2
id: kt-two-compressor-finitary-lef-proof
kind: route
title: Locally quotient the regular SL3 orbits together with every retained finitary permutation
target: kt-two-compressor-normalizer-cocycle-splits
requires:
  - finitary-extension-ce-iff-action-lifts-to-normalizer
  - kt-two-compressor-lamp-orbit-is-a-sofic-regular-wreath
---

The external subgroup `S=SL_3(Z)` acts freely on all of `X=G/Gamma`.
Indeed, if `s in S` fixes `g Gamma`, then `g^(-1)sg in Gamma`; applying the
external projection `G->SL_3(Z)` gives a conjugate of `s` equal to one, so
`s=1`.  Hence, as an `S`-set,

```text
Y ~= disjoint_union_(j in J) S
```

for a countable orbit-index set `J` (including the doubled coordinate).

We prove `Sigma_S=Sym_fin(Y) rtimes S` is LEF.  Fix a finite multiplication
window `F subset Sigma_S`.  Only finitely many orbit labels `J_0 subset J`,
finitely many points `(s,j)` with `j in J_0`, and finitely many translates
of those points by actor words occurring in products from `F` are relevant.
Let `T subset S` be the finite set of all relative positions
`s^(-1)s'` needed to distinguish those points and check those products.

Residual finiteness of `S` supplies a finite quotient `q:S->Q` injective on
`T`.  Send every retained point `(s,j)` to `(q(s),j) in Q x J_0`.  The
injectivity condition identifies the complete finite support of every
retained finitary permutation with a subset of `Q x J_0`.  Transport that
permutation on its support and make it the identity on the complement.  Let
actor elements operate by left translation through `Q`.
All multiplication and conjugation identities in `F` are then exact, and
distinct elements of `F` remain distinct.  This is a local embedding of `F`
into the finite group

```text
Sym(Q x J_0) rtimes Q.
```

Therefore `Sigma_S` is LEF.  LEF groups are sofic and hence hyperlinear, so
`L(Sigma_S)=R rtimes_(alpha|S)S` is Connes embeddable.  The established
normalizer criterion yields `(SPL1)` and the cocycle splitting.

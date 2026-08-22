---
rg: 2
id: positive-density-power-dilation-forces-finite-depth
kind: claim
title: A positive-density power dilation of a strict contraction has bounded depth
distinct_from:
  geometric-infinite-counter-is-hs-trace-diluting: that computes the vanishing density of a standard counter head; this proves the converse quantitative obstruction for every coherent power dilation whose head has positive density.
  finite-game-gap-makes-the-cyclic-acceptance-compressor-strict: that supplies the strict contraction from a game gap; this is the finite-dimensional orbit-capacity theorem which can consume that contraction.
  amplification-natural-words-cannot-read-packet-multiplicity: that rules out reading raw multiplicity from amplification-natural words; this obtains a dimension contradiction without reading multiplicity, by demanding arbitrarily many independent copies of one fixed-density carrier.
---

Let `H` be finite-dimensional, let `Q` be a projection, let `U` be unitary,
and let `T` be a contraction on `QH`.  Suppose

```text
Q U^n Q=T^n                 for 0<=n<=NL,              (PDD1)
||T||<=rho<1.                                                (PDD2)
```

Choose `L` so that

```text
2 rho^L/(1-rho^L)<1,                                     (PDD3)
```

and put

```text
c_rho,L=1-2 rho^L/(1-rho^L)>0.
```

Then the map

```text
V:(QH)^(direct sum (N+1))->H,
V(h_0,...,h_N)=sum_(j=0)^N U^(jL)h_j                  (PDD4)
```

has

```text
||Vh||^2>=c_rho,L sum_j||h_j||^2.                       (PDD5)
```

In particular it is injective, and therefore

```text
(N+1) rank(Q)<=dim(H),
tr_H(Q)<=1/(N+1).                                       (PDD6)
```

Consequently no sequence of finite-dimensional models can have both a fixed
lower density `tr(Q)>=alpha>0` and coherent power-dilation identities
`(PDD1)` to arbitrarily large fixed depth.  Approximate versions also hold:
for each fixed `N,L,rho,alpha`, sufficiently small errors in `(PDD1)--(PDD2)`
contradict `alpha>1/(N+1)`.  No uniformity in `N` is required.

## Proof

For `i<j`, `(PDD1)` gives

```text
<U^(iL)h_i,U^(jL)h_j>
 =<h_i,U^((j-i)L)h_j>
 =<h_i,T^((j-i)L)h_j>.                                  (PDD7)
```

The off-diagonal block in row `i` of the Gram matrix of `V` therefore has
operator norm at most `rho^(|i-j|L)`.  For arbitrary `h_j`, use
`2|<x,Ay>|<=||A||(||x||^2+||y||^2)` and sum the two sides of every diagonal:

```text
||Vh||^2
 >=[1-2 sum_(k>=1)rho^(kL)]sum_j||h_j||^2
 =c_rho,L sum_j||h_j||^2.                               (PDD8)
```

This proves `(PDD5)` and the rank inequality.  The approximate statement
follows because, at fixed `N,L`, the finite block Gram matrix depends
continuously on the finitely many compressed moments and on `T`.

The theorem does not ask a finite approximation to report its dimension.
One first fixes any `N>alpha^(-1)-1`; reverse-Kleene/canonical-profile order
then sends the finitely many relation and moment errors to zero at that fixed
depth.

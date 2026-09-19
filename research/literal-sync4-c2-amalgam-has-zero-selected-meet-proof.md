---
rg: 2
id: literal-sync4-c2-amalgam-has-zero-selected-meet-proof
kind: route
title: Split over the shared sign and compute the two free-projection angles
target: literal-sync4-c2-amalgam-has-zero-selected-meet
requires:
  - sync4-one-negative-abelian-corner-wordizes-arbitrary-pvm
---

The shared involution `s` is central in both abelian vertex groups, hence in
their amalgam `G`.  Therefore `e_+` and `e_-` are central projections of
`L(G)`, each of canonical trace `1/2`.

Write `p_(L,delta)=q_L e_delta` and similarly on the right.  In the
one-negative set there is exactly one character with `s=-1` and exactly
three with `s=+1`.  Every character projection of `(C_2)^4` has canonical
trace `1/16`.  After normalizing the trace in the `e_delta` corner this gives

```text
alpha_-=(1/16)/(1/2)=1/8,
alpha_+=(3/16)/(1/2)=3/8.                              (LSAP1)
```

The reduced group algebra of an amalgamated free product is the reduced
tracial amalgamated free product of the two vertex group algebras over the
edge group algebra.  After compression by either minimal central projection
`e_delta` of `C[<s>]`, the amalgamating algebra is scalar.  Hence
`p_(L,delta)` and `p_(R,delta)` are free projections of common normalized
trace `alpha_delta`.

For completeness, the two-free-projection (free Jacobi) calculation says
that free projections `p,q` of traces `alpha,beta`, with
`alpha+beta<=1`, have no common range and

```text
||pq||=sqrt(alpha(1-beta))+sqrt(beta(1-alpha)).         (LSAP2)
```

This follows by applying the Cauchy transform equation for the free
multiplicative convolution of
`(1-alpha) delta_0+alpha delta_1` and
`(1-beta) delta_0+beta delta_1`: the nonzero spectrum of `pqp` has upper
endpoint

```text
(sqrt(alpha(1-beta))+sqrt(beta(1-alpha)))^2,
```

and its atom at `1` has mass `max(alpha+beta-1,0)`.  In the present equal
trace case `(LSAP2)` becomes `2 sqrt(alpha(1-alpha))`.  Substitution of
`(LSAP1)` gives

```text
||p_(L,-)p_(R,-)||=sqrt(7)/4<1,
||p_(L,+)p_(R,+)||=sqrt(15)/4<1.                       (LSAP3)
```

If a nonzero vector belonged to both ranges in either central corner, their
product would fix that vector and have operator norm at least one,
contradicting `(LSAP3)`.  The meet is zero in both central summands, hence
`q_L meet q_R=0` in `L(G)`.

Finally, a finite graph of finite groups is virtually free.  Finitely
generated virtually free groups are residually finite, so finite quotients
injective on any prescribed finite word ball give exact canonical models of
this amalgam.  They cannot turn the literal edge amalgam into the missing
universal carrier mechanism.


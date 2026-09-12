---
rg: 2
id: toeplitz-swindle-kills-head-k2-sign
kind: claim
title: The algebraic Toeplitz swindle kills every K2 sign imported from a finite head corner
distinct_from:
  toeplitz-finite-head-centralizes-deep-tail: that constructs the orthogonal finite head corners and their tail commutation; this shows why their ordinary Steinberg central signs do not survive in the full Toeplitz ring.
  toeplitz-schur-heads-share-child-but-have-rank-two: that computes a rank-two ceiling for one explicit packet actuator; this rules out a different proposed amplifier using head-corner K2 classes.
---

Let `R` be a regular unital ring and

```text
T_R=R<x,y | yx=1>,       f=1-xy,
I=M_infinity(R)=span{x^i f y^j:i,j>=0}.                 (TSK1)
```

Under the corner/Morita identification `K_2(I)=K_2(R)`, the inclusion

```text
I -> T_R
```

induces the zero map on `K_2`.  In particular, a nontrivial Steinberg symbol
in a finite head corner—such as the order-two symbol `{-1,-1}` over `Z`—is
trivial after mapping to the stable Steinberg kernel over `T_R`.

The point is not special to that symbol.  The Toeplitz extension

```text
0 -> M_infinity(R) -> T_R -> R[t,t^(-1)] -> 0           (TSK2)
```

has boundary map whose Bass summand

```text
K_2(R) <= K_3(R[t,t^(-1)]) -> K_2(M_infinity(R))        (TSK3)
```

is the Morita isomorphism.  Exactness therefore makes the following
inclusion map zero.

Consequently the tempting construction “put a quaternion pair in every
orthogonal Toeplitz head and identify their commutator through the universal
Steinberg center” does not produce a surviving common sign.  Finite head
truncations do carry the common `K_2(R)` class, but the one-sided infinite
compression which makes the ring finitely self-similar swindles that class
away.

This does not rule out a genuinely global central extension of the Toeplitz
elementary group whose cocycle is not imported from the compact ideal.  Such
an extension would need a separate nonzero class in `H^2` and cannot be
obtained by the head-corner Steinberg symbol.

---
rg: 2
id: trace-separation-sphere-distance-concentration-proof
kind: route
title: Haar second moment of a rank-one projector
target: trace-separation-sphere-distance-concentration
requires: []
---

Write `P_x=|x><x|`.  Unitary invariance of Haar measure on the complex sphere
and the symmetric-square moment give

```text
E(P_x tensor P_x) = (I+Flip)/(d(d+1)).
```

This identity is also immediate from Schur's lemma: the expectation is
supported on the symmetric square and has trace one, whose dimension is
`d(d+1)/2`.

For any `A in M_d(C)`, contracting against `A tensor A^*` yields

```text
E |<x,Ax>|^2
 = (Tr(AA^*) + |Tr A|^2)/(d(d+1)).
```

Since `E <x,Ax> = Tr(A)/d = tau(A)`, subtraction gives

```text
E |<x,Ax>-tau(A)|^2
 = (tau(AA^*)-|tau(A)|^2)/(d+1).
```

Take `A=D=U^*V`, for which `D D^*=I`.  This proves the displayed exact
complex variance formula.  Finally

```text
Z(x)
 = <x,(U-V)^*(U-V)x>
 = 2 - 2 Re <x,Dx>.
```

Therefore `E Z=2-2 Re tau(D)`, and

```text
Var(Z)
 = 4 Var(Re <x,Dx>)
 <= 4 E |<x,Dx>-tau(D)|^2
 = 4(1-|tau(D)|^2)/(d+1).
```

Chebyshev gives the tail estimate.  For finitely many tested word pairs, sum
the tail probabilities.  If desired one may force the ambient dimension to
tend to infinity without changing a microstate's normalized-HS defects or
normalized traces by taking block-diagonal direct-sum copies, so this
concentration never imposes a dimension-growth hypothesis on hyperlinearity.

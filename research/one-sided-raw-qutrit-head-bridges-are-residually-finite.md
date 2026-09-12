---
rg: 2
id: one-sided-raw-qutrit-head-bridges-are-residually-finite
kind: claim
title: A qutrit head bridge with only one raw direction remains residually finite
artifacts:
  - research/one-sided-raw-qutrit-head-proof.md
distinct_from:
  qutrit-head-only-overlap-envelope-is-finite: that permits only coefficients in F_2[Q] and obtains a finite group; this adds one unbounded raw direction and obtains an infinite but residually finite group.
  depth-mismatched-qutrit-root-bridge-is-residually-finite: that uses the polynomial ring F_2[T] without the head idempotent; this includes the head and proves residual finiteness of the resulting noncommutative one-sided coefficient algebra.
  one-balanced-actor-qutrit-bridge-is-jacobson-core: that includes both S and T with TS=1 and is not residually finite; this proves that neither raw direction separately reaches that boundary.
---

Let

```text
A_+=F_2<S,Q | Q^2=Q, QS=0>,
A_-=F_2<T,Q | Q^2=Q, TQ=0>.                             (ORQ1)
```

Both algebras embed as the indicated subalgebras of
`J=F_2<S,T | TS=1>`, where `Q=1-ST`, and both are residually finite
dimensional over `F_2`.

Let `K=GL_28(F_2)` be the finite scalar qutrit envelope.  In the outer
leaf chart,

```text
H_+=<K,x_12(S),x_12(Q)> = EL_28(A_+),
H_-=<K,x_12(T),x_12(Q)> = EL_28(A_-).                   (ORQ2)
```

Consequently `H_+` and `H_-` are residually finite, hence sofic and
hyperlinear.  The same holds for every subgroup supported by finitely many
roots whose coefficients remain in either one-sided algebra.

Thus a noncentral qutrit/head overlap does not escape merely by mentioning
one raw coefficient.  The first non-residually-finite coefficient return must
use both directions in one incidence and consume `TS=1`; the balanced
actor of `one-balanced-actor-qutrit-bridge-is-jacobson-core` is minimal in
this exact sense.

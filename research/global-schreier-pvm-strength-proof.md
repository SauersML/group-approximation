---
rg: 2
id: global-schreier-pvm-strength-proof
kind: route
title: Apply the Schreier gap and push an equivariant Bernoulli PVM to the orbit
target: global-schreier-pvm-is-stronger-than-action-soficity
requires:
  - infinite-schreier-pvm-transport-kills-finite-mark
  - no-invariant-mean-on-coset-space
---

Equation `(GSP2)` is exactly `(ISP3)` applied at each matrix level, and
passing to the limit proves `mu=0`.

For strictness versus soficity, take an infinite finitely generated
nonamenable sofic group `H` acting on itself. Its regular action is sofic,
while the regular Schreier graph has positive bottom gap for a suitable
finite symmetric generating set. If it admitted `(GSP1)` with positive
mass, `(GSP2)` would contradict it. Hence action soficity cannot imply
global Schreier-PVM extraction.

For the Bernoulli statement, exact covariance gives

```text
tau(E_(ax))=tau(aE_xa^*)=tau(E_x).                     (GSS1)
```

If `R=sum_xE_x` is nonzero and invariant, countable additivity of the normal
trace makes `(GSP6)` a probability measure, and `(GSS1)` makes it invariant.
No such measure exists on the infinite non-coamenable transitive orbit.
Finally `(GSP5)` is ordinary independence of two Bernoulli coordinates.

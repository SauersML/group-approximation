---
rg: 2
id: fournier-facio-has-no-purely-singular-free-near-representation
kind: claim
title: The Fournier--Facio group has no purely singular essentially free amenable near representation
distinct_from:
  fournier-facio-purely-singular-free-near-representation: That is the positive branch and is exactly the negation of this claim.
  near-representation-amenability-dichotomy: That asks for a general charge-visible Kazhdan theorem; this asks only for exclusion of the canonical witness for one explicit group.
---

There do not exist `H`, a purely singular invariant state `phi` on `B(H)`,
and a `phi`-near representation `pi:G -> U(H)` in the Kahl--Schneider state
sense with

```text
phi(pi(g))=0                    for every g != 1.
```

By `fournier-facio-hyperlinear-iff-singular-near`, this is the negative
hyperlinearity branch for the explicit finitely presented torsion-free
Fournier--Facio group.

## Attempts

Because `G` is non-residually-finite and Kazhdan, the established
`non-rf-kazhdan-weak-ucp-iff-non-hyperlinear` theorem would prove this claim
from weak ucp-stability (or from LLP of the full group C-star algebra).  No
such stability or LLP theorem is known for this group.  Its operator-norm and
unnormalized-Frobenius stability do not imply weak ucp-stability, and the
compression defect alone is trace-blind in normalized HS.  Thus the direct
attack is deferred to a genuinely normalized-HS/ucp argument.

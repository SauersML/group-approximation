---
rg: 2
id: normal-finite-role-packet-router-proof
kind: route
title: Apply Schur normal form and the two-term operator-Schmidt decomposition
target: normal-finite-role-packets-cannot-route-controlled-payloads
requires: []
artifacts:
  - research/artifacts/hybrid-rank-router-tensor-closure-2026-08-23.md
---

On the selected isotypic carrier, conjugation by a normalizer word restricts
to an automorphism of the full packet factor.  Remove an inner implementer;
Schur's lemma gives `(NFR1)`.

Normalize the role and multiplicity traces.  Since `p` is balanced and
`tau(A)=0`, the two summands

```text
p tensor A,             (1-p) tensor I
```

are orthogonal in Hilbert--Schmidt space and each has norm `1/sqrt(2)`.
They are a Schmidt decomposition of the unit vector `T`.  Its inner product
with any unit simple tensor is therefore at most `1/sqrt(2)`.  Both `T` and
`C tensor W` are unitaries, so

```text
||T-C tensor W||_2^2
 =2-2 Re <T,C tensor W>
 >=2-sqrt(2).
```

Finally set `B=I` in the claimed hybrid routing identity.  Both hybrid
outputs become `T`, contradicting the fixed positive distance from every
normalizer word.  This proves the stated finite-normal-packet firewall.

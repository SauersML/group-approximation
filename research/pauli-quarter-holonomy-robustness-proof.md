---
rg: 2
id: pauli-quarter-holonomy-robustness-proof
kind: route
title: Expand the reflection commutator into two fixed projection moments
target: canonical-trace-tests-robustify-pauli-quarter-holonomy
requires: []
---

For projections `P,Q`, set `R=2P-I`, `S=2Q-I`.  Direct expansion gives

```text
||RSRS-I||_2^2=||RS-SR||_2^2
               =16||PQ-QP||_2^2
               =32(tau(PQ)-tau(PQPQ)).
```

Indeed `tau(QPQP)=tau(PQPQ)` and `tau(QPQ)=tau(PQP)=tau(PQ)`.  In the atlas
quarter packet,

```text
tau(PQ)=1/16,   tau(PQPQ)=3/64,
```

so the displayed norm is exactly `1/2`.  Moreover `(RS)^4=I`; the square
`(RS)^2` is the nontrivial central dihedral involution and its negative cut
has fixed positive trace.

Only finitely many packet words occur in these two moments.  Exactify the
fixed finite involution packet, spectrally round the resulting almost
projections, and telescope each of those finitely many words.  Cauchy--
Schwarz then changes the two moments by at most
`C(def+sep_F)`, for a fixed computable `C` and word window `F`.  Substitution
in the exact identity yields

```text
||R(U)S(U)R(U)S(U)-I||_2^2
 >=1/2-C(def(U)+sep_F(U)),
```

uniformly in dimension.

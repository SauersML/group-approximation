---
rg: 2
id: atlas-a4-multiplicity-wire-gauges-are-asymptotically-trivial-proof
kind: route
title: Lipschitz coherence transports plus near-identity Schur gauges kill local multiplicity rotation
target: atlas-a4-multiplicity-wire-gauges-are-asymptotically-trivial
requires:
  - atlas-a4-context-near-identity-schur-gauges
  - a4-canonical-coherence-data-hs-lipschitz
---

For one context suppress `c,n` from the notation.  Let `T` be its canonical
partial unitary `R_0 H -> S H`, and `T'` the corresponding partial unitary for
the literal chart A4 pair.  By
`atlas-a4-context-near-identity-schur-gauges`, the two exact A4 generator pairs
are `o(1)` apart and there is an exact intertwiner `Z` with

```text
||Z-I||_2=o(1).                                       (1)
```

By `a4-canonical-coherence-data-hs-lipschitz`, their canonical transports and
carrier projections satisfy

```text
||T'-T||_2=o(1),
||S'-S||_2=o(1).                                       (2)
```

The multiplicity transport extracted from the exact Schur gauge is

```text
V=T' Z T^*.
```

Since `T T^*=S`, operator-norm contractivity of the partial unitaries and
`(1)--(2)` give

```text
||V-S||_2
 <= ||(T'-T) Z T^*||_2 + ||T (Z-I) T^*||_2
 <= ||T'-T||_2 + ||Z-I||_2
 = o(1).                                               (3)
```

Thus `V` is asymptotically the identity partial isometry on the carrier.  The
same calculation works for every branch `j`.  Exact A4 intertwining and the
canonical Schur factorization force the resulting multiplicity maps to agree,
so the branch chosen to read the wire is irrelevant.

There are only thirty contexts, hence the maximum of the finitely many `o(1)`
errors is again `o(1)`.  This proves `(A4-WIRE-ID)` uniformly.
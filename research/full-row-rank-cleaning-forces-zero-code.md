---
rg: 2
id: full-row-rank-cleaning-forces-zero-code
kind: claim
title: Full-row-rank LDPC erasure cleaning forces the code to vanish
distinct_from:
  collective-cofilling-is-common-erasure-cleaning: that constructs cleaning from redundant cochain checks; this rules out full-row-rank positive-distance Tanner presentations.
  erasure-cleaning-rounds-all-projective-parity-valleys: that assumes cleaning abstractly; this extracts a necessary check-dependency condition from singleton erasures.
---

Let `H:F_2^L -> F_2^M` have full row rank, column degree at most `d`, and
let `M>=rho L`.  Suppose singleton instances of common-support erasure
cleaning hold with constant `K`:

```text
ker(H_(rows other than e)) <= ker(H)+F_2^S_e,
|S_e| <= K L/M.                                          (FRC1)
```

Then `C=ker(H)` has a generating projection `P:F_2^L -> C` whose columns
have weight at most

```text
1+d ceil(K/rho).                                         (FRC2)
```

Consequently, if the minimum distance of `C` is larger than `(FRC2)`, then
`C=0`.  In particular, no positive-dimensional family with linear distance,
bounded column degree and `M=Theta(L)` can have both full row rank and
uniform common-support erasure cleaning.  Substantial redundant-check
dependencies are necessary; the redundancy in higher-dimensional
coboundary presentations is structural, not cosmetic.

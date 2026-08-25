---
rg: 2
id: hecke-square-covariance-authentication
kind: route
title: Authenticate the Hecke maps from their squares and the separate native covariance rows
target: center-chain-common-source-authenticates-native-covariances
requires:
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
  - center-chain-mixed-hecke-polars-share-a1-tail
---

**INVALIDATED PROJECTIVE-DATA PROPOSAL.**  Use

```text
u_1^2=x_87(s_(00)t_0),
u_2^2=x_98(s_(000)t_(00))
```

to identify the two common-source Hecke polars with the two native
coefficient transports, and use the separate native source/controlled-target
conjugation rows to recover the desired selector types.  All source/range
and mixed-Pauli data would then be supplied by the exact common-source
calculation.

`projective-row-data-do-not-authenticate-hecke-polars`
invalidates this inference.  Tensoring either candidate native transport by
a balanced spectator involution preserves its square, supports, and every
separate covariance row exactly, but makes it Hilbert--Schmidt orthogonal to
the ungauged Hecke polar and every fixed packet-label relabeling.  The
surviving proof must use an odd-parity mixed occurrence anchor from the full
coefficient presentation; projective row data alone cannot close the leaf.

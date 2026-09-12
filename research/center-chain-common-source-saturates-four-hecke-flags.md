---
rg: 2
id: center-chain-common-source-saturates-four-hecke-flags
kind: claim
title: The exact center-chain common source saturates all four numerical Hecke flags
distinct_from:
  center-chain-four-hecke-flags-have-native-ranks: that computes four different ambient e-corner ranks; this proves all four flags become the identity after restriction to the exact common source.
  center-chain-common-source-authenticates-native-covariances: that asks for separately typed native source and target maps; this shows why the four ambient rank matches cannot supply that typing on the common source.
---

**ESTABLISHED EXACT NO-GO.**  Retain the four projections
`r_1,r_2,p_1,p_2` of `(FHF2)` and the exact common source
`Q=e_(L_0,lambda_0)` of `(MCS3)--(MCS4)`.  Then

```text
r_1Q=r_2Q=p_1Q=p_2Q=Q.                                (CSF1)
```

Consequently, on every nonzero subprojection `E<=Q`, all four compressed
flag projections equal `E`.  The unequal ambient `e`-corner ranks
`1/2,1/4,1/4,1/8` are completely erased by passage to the common source.
Hence those ranks cannot authenticate the two native rows on `Q`; any
successful construction must provide separately typed native maps rather
than reusing the four Hecke supports.

DERIVATION
center-chain-common-source-saturation-proof


---
rg: 2
id: leavitt-native-strict-kazhdan-compression-pair
kind: claim
title: "The native four-by-four Leavitt configuration is a strict finitely generated Kazhdan compression pair"
distinct_from:
  openai-nine-leaf-leavitt-configuration: "That constructs the earlier nine-leaf pair; this specifies the native rank-four pair and its explicit strictness witness."
artifacts:
  - research/artifacts/leavitt-direct-normalization-obstruction-2026-09-20.md
---


For R=L_(F_2)(1,2), identify Q=R^x with EL_4(R), and put
L=diag(EL_3(R),1). Both Q and L have property (T). The matrices
u,k_+,k_- in the artifact satisfy

```text
Q=<L,u,k_+,k_->,
uLu^-1 < L,       k_+ L k_+^-1 = k_- L k_-^-1 = L.
```

Strictness has the explicit witness x_12(e), where e=ab=1-st:
x_12(e) belongs to L but not to uLu^-1. This is an algebraic and
property-(T) configuration; neither normalization, nonhyperlinearity,
simplicity nor finite presentation is assumed. The finite-presentation
input is imported separately by the Rips consumers.

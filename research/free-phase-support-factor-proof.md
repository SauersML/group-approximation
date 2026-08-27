---
rg: 2
id: free-phase-support-factor-proof
kind: route
title: Rewrite every phase difference in a Nielsen basis
target: free-phase-context-support-is-a-proper-free-factor
requires:
  - one-binary-marginal-block-escape
---

Starting with the free basis `(h_1,...,h_D)`, replace `h_i` by
`h_i h_1^(-1)` for `i=2,...,D`.  These elementary Nielsen moves produce the
basis `(FPS2)`, proving that `L_D` is a rank-`D-1` free factor and that
`F_D=L_D * <h_1>`.

Because the free factor commutes with the root group,

```text
W E_(ij)W^*=h_i E_(ij)h_j^(-1)=E_(ij)h_i h_j^(-1).
```

Substituting `h_i=a_i h_1` gives
`h_i h_j^(-1)=a_i a_j^(-1)` and proves `(FPS3)--(FPS4)` by linearity.
The off-diagonal support assertion is the same reduced-word coefficient
calculation as `(OBM6)`.

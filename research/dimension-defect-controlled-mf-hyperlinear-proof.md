---
rg: 2
id: dimension-defect-controlled-mf-hyperlinear-proof
kind: route
title: Apply the same padded tensor exponent to every pair in each local MF window
target: dimension-defect-controlled-mf-hyperlinear
requires:
  - adaptive-tensor-amplification
artifacts:
  - research/artifacts/adaptive-tensor-amplification-2026-08-19.md
---

## Why sufficient

Normalize the local MF models so every distinct pair in the current finite
window has operator distance at least `1`.  For the whole model use the single
post-processing

```text
W_n(g)=(V_n(g) directSum 1_(d_n))^(tensor p_n),
p_n=ceil(8 d_n).
```

For any distinct `g,h` in the window,

```text
W_n(g)^*W_n(h)
 = ((V_n(g)^*V_n(h)) directSum 1)^(tensor p_n),
```

so `adaptive-tensor-amplification` gives the same absolute normalized
2-separation for every pair.  The operator defect of `W_n` is at most
`p_n epsilon_n`, hence its 2-defect is also at most that quantity and tends
to zero because `d_n epsilon_n->0`.

Taking these models along an exhaustion is exactly the local-to-global
hyperlinear construction.  No pair-specific block sum is needed, so there is
no hidden dilution by unequal block dimensions.

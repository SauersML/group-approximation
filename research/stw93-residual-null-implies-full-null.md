---
rg: 2
id: stw93-residual-null-implies-full-null
kind: route
title: Pull residual annihilation back across the Jiang--Su null quotient
target: stw93-trace-kernel-quasitracial-invisibility
requires:
  - stw93-jiang-su-slice-ideal-is-quasitrace-null
  - stw93-residual-trace-kernel-is-quasitrace-null
---

Let `π:D→D/K_𝒵` be the quotient map and let `q` be a normalized
`2`-quasitrace on `D`.  The Jiang--Su-slice ideal theorem gives a unique
normalized quasitrace `q-bar` on `D/K_𝒵` such that `q=q-bar∘π`.
For `x∈I_+`, the image `π(x)` belongs to `(I/K_𝒵)_+`, so residual
annihilation gives

```text
q(x)=q-bar(π(x))=0.
```

Thus every normalized quasitrace on `D` annihilates `I`.

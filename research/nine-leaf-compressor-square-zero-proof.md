---
rg: 2
id: nine-leaf-compressor-square-zero-proof
kind: route
title: Swap the auxiliary prefix families and square one plus the relative involution
target: nine-leaf-compressor-sum-is-square-zero-packet
requires:
  - openai-nine-leaf-leavitt-configuration
artifacts:
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
---

The two prefix tables agree on every `alpha_i` cylinder and exchange which of
the `beta` and `nu` families maps to the `alpha_i1` and `zeta_i` families.
Consequently `c=v^(-1)u` fixes the `alpha` cylinders, swaps the two auxiliary
families, has order two, and centralizes `Gamma`, which is supported on the
fixed `alpha` block.

In characteristic two, `n=1+[c]` has `n^2=0`.  Since

```text
[u]+[v]=[v]n,
[u^(-1)]+[v^(-1)]=n[v^(-1)],
```

and `n` commutes with every `a in F_2[Gamma]`, the displayed sandwich equals
`[v]nan[v^(-1)]=[v]a n^2[v^(-1)]=0`.

---
rg: 2
id: regular-tensor-moving-root-proof
kind: route
title: Raise the amplified roots to their quotient orders
target: regular-tensor-camouflage-preserves-moving-root-failures
requires:
  - residual-finite-tensor-camouflages-iwahori-transfer-failures
---

Since `lambda_n(u)^(N_n)=1`, the tensor-power rule gives `(RTM1)`.
Thus every polynomial in `pi_(n,+)(u)^(N_n)` is the same polynomial in
`(U'_n)^(N_n)` tensored with `1`.  Repeat for the lower root.

For payload matrices `A,B`,

```text
||(A tensor 1)(B tensor 1)||_2=||AB||_2,
||[A tensor 1,B tensor 1]||_2=||[A,B]||_2.
```

The edge-defect and fixed-character assertions are exactly those proved by
the required camouflage node.  Hence both regularity and the moving payload
geometry coexist in the amplified sequence.


---
rg: 2
id: schur-toeplitz-envelope-self-embedding-proof
kind: route
title: Add the packet augmentation on the defect head and compress everything else
target: schur-toeplitz-envelope-has-proper-self-embedding
requires:
  - schur-idempotent-is-an-injective-toeplitz-defect
---

The forbidden idempotent is supported in the marked `J=-1` packet sector,
so the trivial packet character kills it. It therefore extends with
`x,y->1` to `(SSE1)`. Expand the product of two expressions `(SSE2)`.
The two cross terms vanish by `P_fx=0` and `yP_f=0`; the remaining terms are
`xaby+epsilon(ab)P_f`. Also `sigma(1)=xy+P_f=1`. Multiplication on the left
by `y` and on the right by `x` gives the stated left inverse. Iteration on
`P_f`, whose augmentation is zero, gives `(SSE3)`. If `P_f` had a preimage,
the left inverse would make that preimage `yP_fx=0`, so injectivity would
force `P_f=0`. Thus the endomorphism is proper.

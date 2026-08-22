---
rg: 2
id: fd-invisible-anchor-localization-no-go-proof
kind: route
title: Tensor the Slofstra--Vidick invisible mark with an exact two-point anchor packet
target: fd-invisible-anchor-does-not-localize-bcs-consistency
requires:
  - exact-fd-invisibility-has-no-general-hs-robustification
  - bcs-commuting-square-transfer-collapses-britton-commutator
  - leavitt-prefixes-form-exponential-heisenberg-packet
  - canonical-iwahori-transfer-is-equivalent-to-full-transfer
---

Take the direct product of the established finitely presented sofic witness
`(K,c)` with `C_2`.  Products of sofic groups are sofic, and product sofic
approximations can keep the finite factor exact.  With `q=(1+s)/2`, exact
finite-dimensional invisibility gives `(FIA3)`.

In the product regular trace, `q` belongs to the finite factor while `c`
belongs to `K`.  Thus trace factorization and `tau_K(c)=0` give

```text
tau(q(c-1)^*(c-1)q)
 =tau_C2(q) tau_K(2-c-c^*)
 =(1/2) 2=1.
```

Moment convergence gives `(FIA4)`, disproving localized robustification even
for a named central reducing carrier.

For `(FIA7)`, centrality permits cyclically moving `w-1` past every `Q_i`:

```text
sum_i ||(w-1)Q_i||_2^2
 =tau((w-1)^*(w-1) sum_i Q_iQ_i^*)
 >=kappa ||w-1||_2^2.
```

Finally `(FIA8)` follows from `(J-1)e_-=-2e_-` and
`(J-1)e_+=0`.  The BCS and arithmetic conclusions then follow from the two
required established audits; no additional approximation theorem is used.

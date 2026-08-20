---
rg: 2
id: embedded-packet-projection-relator-ideal-proof
kind: route
title: Evaluate the proposed certificate in the group algebra and left regular trace
target: embedded-packet-projection-has-no-relator-ideal-certificate
requires: []
---

Let `F(S)` be the free group. The presentation quotient induces

```text
C[F(S)] -> C[Gamma].
```

Every factor `r_t-1` in `(EPC1)` maps to zero, so its right side maps to
zero. Since `H->Gamma` is injective, its distinct elements remain distinct
basis vectors of `C[Gamma]`; hence the induced linear map
`C[H]->C[Gamma]` is injective. The nonzero left side cannot map to zero.

For the analytic statement, let `lambda_Gamma` act on `l2(Gamma)` and use
the canonical group trace. It is faithful on `C[Gamma]`, so

```text
||lambda_Gamma(A)||_2^2=tau(A^*A)>0.
```

Every defining relator evaluates to the identity. Thus the right side of
`(EPC2)` is zero, proving the contradiction.

---
rg: 2
id: two-point-qutrit-tensor-closure-no-go-proof
kind: route
title: Tensor two false and two true scalar clocks back into the omega sector
target: two-point-qutrit-spectrum-is-not-fixed-sector-group-gadgetizable
requires: []
---

Choose exact completeness representations `rho_1,rho_2` with
`rho_i(J)=omega I` and `rho_i(u)=omega I`, and `rho_3,rho_4` with
`rho_i(J)=omega I` and `rho_i(u)=I`.  Their tensor product `rho` is a group
representation because evaluation of every word tensorizes.  In particular
all gadget relators remain exact, including relators involving arbitrary
noncommuting auxiliaries.  Direct multiplication gives

```text
rho(J)=omega^4 I=omega I,
rho(u)=omega^2 I.
```

Thus `rho` lies in the soundness sector, while
`Pi_(omega^2)(rho(u))=I`, contradicting `(TQS1)`.  A fixed amplification in
the completeness clause only tensors extra identity multiplicities and does
not change either scalar calculation.

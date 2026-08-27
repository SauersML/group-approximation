---
rg: 2
id: bs14-global-threshold-ledger-proof
kind: route
title: Balance active rank against passive source coupling at tau equals e one-quarter
target: bs14-energy-threshold-active-passive-ledger
requires:
  - scalar-bs14-exit-angle-energy-dichotomy
---

For every eigenvalue `a_j`, `(SAE6)` gives

```text
f(a_j)>=(3/8)(1-a_j^2)^2.
```

Each active direction therefore contributes at least `(3/8)tau^2` to
`E`, proving

```text
rank(Q_active)<=8E/(3tau^2).
```

Divide by `d` and substitute `tau=e^(1/4)` to obtain `(ATL3)`.  On the
passive directions,

```text
||PXQ_passive||_F^2=sum_passive(1-a_j^2)<=tau rank(Q)<=tau d,
```

which gives `(ATL4)`.  No carrier angle or packet phase appears in either
estimate.


---
rg: 2
id: closed-multiplicity-cycle-trace-proof
kind: route
title: Cyclic trace unfolds an expanding return cycle into a geometric error ledger
target: closed-multiplicity-cycle-kills-carrier-trace
requires: []
---

Put `c_e=tr(P_e)`.  Cyclicity of matrix trace gives, for every edge and
branch,

```text
tr(S_(e,j) T_(e,j))=tr(T_(e,j) S_(e,j)).
```

Since normalized trace has norm one on normalized Hilbert--Schmidt space,

```text
|c_(e+1)-r_e c_e|
 <= sigma_e + sum_j epsilon_(e,j) =: delta_e.              (1)
```

Write `eta_e=c_(e+1)-r_e c_e`.  Iterating these scalar identities gives

```text
c_m = R c_0 + sum_(e=0)^(m-1) R_(>e) eta_e.                (2)
```

Also `|c_m-c_0| <= ||P_m-P_0||_2=rho`.  Subtract `c_0` from (2), use
`|eta_e|<=delta_e`, and obtain `(CMC1)`.

If every `r_e=2` and every individual displayed defect is at most
`epsilon`, then `delta_e<=3 epsilon` and

```text
sum_(e=0)^(m-1) R_(>e)=sum_(q=0)^(m-1)2^q=2^m-1.
```

Dividing `(CMC1)` by `2^m-1` proves `(CMC2)`.  No contraction, rank, or
integrality assumption on the decoded block maps is used; the entire endpoint
is finite cyclic trace plus identification of the returned projection.

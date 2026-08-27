---
rg: 2
id: clifford-inverse-sqrt-log-ledger-proof
kind: route
title: Sum the challenge rows and cross the exact Clifford capacity threshold
target: clifford-total-energy-ledger-has-inverse-sqrt-log-critical-rate
requires:
  - robust-clifford-capacity-bound
---

If every row were smaller than the right side of `(CTL3)`, then `(CTL2)`
would give `epsilon<kappa`.  Hence `epsilon<1/16` and
`42 epsilon<rho`, so `robust-clifford-capacity-bound` yields

```text
dim(corner)>=2^(floor(n(d)/2)-1)
            =2^(floor(log_2 d)+1)>d,
```

a contradiction.  For `(CTL4)`, orthogonality gives `tr(p_j)=1/n`, so the
displayed norm and sum are immediate.

---
rg: 2
id: bounded-cycle-polylogarithmic-error-proof
kind: route
title: Compare the lcm level and the cubic-order congruence quotient
target: bounded-cycle-level-has-only-polylogarithmic-error
requires: []
---

The left inequality in `(PLE2)` holds because `4^K-1` is one of the terms
in the least common multiple.  The right inequality follows from

```text
N_K <= product_(m=1)^K(4^m-1)
    <  product_(m=1)^K 4^m
    =  4^(K(K+1)/2).                                  (PPP1)
```

By `one-unipotent-iwahori-quotients-are-bounded-congruence-extensions`,

```text
log |Q_K|=3 log N_K+O_Gamma(1).                        (PPP2)
```

The lower bound on `N_K` gives `K=O(log |Q_K|)`, hence
`K^(-1/2)>=c(log |Q_K|)^(-1/2)`.  The upper bound gives
`log |Q_K|=O(K^2)`, hence
`K^(-1/2)<=C(log |Q_K|)^(-1/4)`.  Multiplying by the fixed word-Lipschitz
constant `C_*` proves `(PLE3)`.

A power-law certificate such as `delta_K>=c|Q_K|^(-A)` or
`delta_K>=cN_K^(-A)` is a positive lower bound, but it lies below
`alpha_K` for large `K` and therefore cannot verify `alpha_K<delta_K/2`.
No assertion about the unknown optimal `delta_K` follows.

